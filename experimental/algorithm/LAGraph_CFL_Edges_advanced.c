//------------------------------------------------------------------------------
// LAGraph_CFL_Edges_advanced.c: Advanced extraction of terminal edges involved
// in at least one Context-Free Language (CFL) derivation for selected pair sets.
//
// Key Optimizations:
//  - De-multiplexed Frontier by non-terminal symbol A (CFL_Frontier).
//  - 16-byte state items {i, j} with 64-bit GrB_Index.
//  - 11-bit LSD Radix Sort with bitwise mask-based pass skipping (OR ^ AND).
//  - Hybrid fallback to qsort for small frontiers (n < 512).
//  - Merging F = {j_1 < j_2 < ... < j_m} with rows of matrices B, C and adj[a]
// using cfl_gallop_search.
//  - Zero-copy HyperCSR unpack without GrB_Matrix_dup, qsort, or dense row
// offsets.
//  - Usage of PathsView (bucket index), RowPresence, and visited bitsets.
//------------------------------------------------------------------------------

#include "LG_internal.h"
#include <LAGraphX.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

// Memory budget divisor for bucket index allocation.
#define BUCKET_MEM_BUDGET_DIVISOR 4

// Maximum range size threshold for switching from binary search to linear scan.
#define BINARY_SEARCH_THRESHOLD 8

// Radix sort parameters for vertex pair queue sorting.
#define RADIX_BITS 11
#define RADIX_SIZE (1u << RADIX_BITS)
#define SORT_SMALL 512

#define LG_FREE_WORK                                                                     \
    do {                                                                                 \
        if (R != NULL) {                                                                 \
            for (size_t i_ = 0; i_ < symbols_amount; i_++) {                             \
                GrB_free(&R[i_]);                                                        \
            }                                                                            \
        }                                                                                \
        LAGraph_Free((void **)&R, NULL);                                                 \
        LAGraph_Free((void **)&new_rules, NULL);                                         \
        free(triples);                                                                   \
        triples = NULL;                                                                  \
    } while (0)

// Binary rule A -> B C
typedef struct {
    int32_t A; // Left-hand side symbol
    int32_t B; // First symbol on the right-hand side
    int32_t C; // Second symbol on the right-hand side
} CFL_triple;

// Terminal rule A -> a
typedef struct {
    int32_t A; // Left-hand side symbol
    int32_t a; // Right-hand terminal symbol
} CFL_TermRule;

// Represents a pair of vertex indices (i, j) in graph traversal
typedef struct {
    GrB_Index src_node;
    GrB_Index dst_node;
} CFL_VertexPair;

// Dynamic queue for vertex pairs associated with a specific nonterminal symbol
typedef struct {
    CFL_VertexPair *v;
    size_t n, cap;
} CFL_PairQueue;

// De-multiplexed BFS frontier holding pair queues for all nonterminals
typedef struct {
    CFL_PairQueue *q;    // Array of pair queues [symbols_amount]
    int32_t *active;     // Nonterminals with non-empty queues at current BFS level
    size_t active_count; // Number of active nonterminals
} CFL_Frontier;

// Resolves pattern role IDs based on mask, rows, columns, and index offsets.
static inline int32_t pat_role_id(const LAGraph_Pat_role *role, int64_t mask,
                                  int64_t qrow, int64_t qcol, int64_t idx) {
    if (role->kind == LAGraph_PAT_SYM_PLAIN) {
        return role->base + (int32_t)idx;
    }
    return role->base + (int32_t)(mask * role->mask_stride + qrow * role->qrow_stride +
                                  qcol * role->qcol_stride + idx);
}

// Validates and appends a binary CFL triple into the dynamically resizing triples buffer.
#define EMIT(pa, pb, pc)                                                                 \
    do {                                                                                 \
        int32_t a_ = (pa), b_ = (pb), c_ = (pc);                                         \
        if (a_ >= 0 && b_ >= 0 && c_ >= 0 && (size_t)a_ < symbols_amount &&              \
            (size_t)b_ < symbols_amount && (size_t)c_ < symbols_amount &&                \
            R[a_] != NULL && R[b_] != NULL && R[c_] != NULL) {                           \
            if (triples_count == triples_cap) {                                          \
                size_t ncap = triples_cap ? 2 * triples_cap : 64;                        \
                if (ncap < triples_cap || ncap > SIZE_MAX / sizeof(CFL_triple)) {        \
                    info = GrB_OUT_OF_MEMORY;                                            \
                    goto cleanup;                                                        \
                }                                                                        \
                CFL_triple *tmp_ = realloc(triples, ncap * sizeof(CFL_triple));          \
                if (tmp_ == NULL) {                                                      \
                    info = GrB_OUT_OF_MEMORY;                                            \
                    goto cleanup;                                                        \
                }                                                                        \
                triples = tmp_;                                                          \
                triples_cap = ncap;                                                      \
            }                                                                            \
            triples[triples_count++] = (CFL_triple){a_, b_, c_};                         \
        }                                                                                \
    } while (0)

// Zero-copy view wrapper around GraphBLAS HyperCSR matrices for fast indexed access.
typedef struct {
    GrB_Matrix mat;
    GrB_Index *Ap;
    GrB_Index *Ah;
    GrB_Index *Aj;
    void *Ax;
    GrB_Index Ap_size;
    GrB_Index Ah_size;
    GrB_Index Aj_size;
    GrB_Index Ax_size;
    GrB_Index nvec;
    GrB_Index nnz;
    bool iso;
    bool open;
    uint64_t *visited;
    uint32_t *bstart;
    uint32_t shift;
    GrB_Index nbuckets;
} PathsView;

typedef struct {
    size_t words;
    uint64_t *bits;
} RowPresence;

typedef struct {
    int32_t B;
    int32_t C;
} BinRule;

typedef struct {
    BinRule *rules;
    size_t *offset;
} BinaryIndex;

typedef struct {
    int32_t a;
} TermRule;

typedef struct {
    TermRule *rules;
    size_t *offset;
} TermIndex;

typedef struct {
    GrB_Index *rows;
    GrB_Index *cols;
    size_t n;
    size_t cap;
} CFL_EdgeBuffer;

static inline size_t cfl_grow_capacity(size_t current_cap, size_t min_needed) {
    if (current_cap == 0) {
        return min_needed > 256 ? min_needed : 256;
    }
    size_t new_cap = current_cap + (current_cap >> 1); // Grow by factor of 1.5
    if (new_cap < min_needed) {
        new_cap = min_needed;
    }
    return new_cap;
}

// Exponential search (galloping search) helper to locate elements in sorted arrays.
static inline GrB_Index cfl_gallop_search(const GrB_Index *arr, GrB_Index pos,
                                          GrB_Index len, GrB_Index target_val) {
    if (pos >= len || arr[pos] >= target_val) {
        return pos;
    }
    GrB_Index step = 1;
    while (pos + step < len && arr[pos + step] < target_val) {
        pos += step;
        step <<= 1;
    }
    GrB_Index low = pos;
    GrB_Index high = (pos + step < len) ? (pos + step) : len;
    while (low < high) {
        GrB_Index mid = low + (high - low) / 2;
        if (arr[mid] < target_val) {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    return low;
}

static inline GrB_Info cfl_pair_queue_push(CFL_PairQueue *q, CFL_VertexPair pair) {
    if (q->n == q->cap) {
        size_t nc = cfl_grow_capacity(q->cap, q->n + 1);
        if (nc < q->cap || nc > SIZE_MAX / sizeof(CFL_VertexPair)) {
            return GrB_OUT_OF_MEMORY;
        }
        CFL_VertexPair *p = realloc(q->v, nc * sizeof(CFL_VertexPair));
        if (!p) {
            return GrB_OUT_OF_MEMORY;
        }
        q->v = p;
        q->cap = nc;
    }
    q->v[q->n++] = pair;
    return GrB_SUCCESS;
}

static int cfl_compare_vertex_pairs(const void *a, const void *b) {
    const CFL_VertexPair *x = (const CFL_VertexPair *)a;
    const CFL_VertexPair *y = (const CFL_VertexPair *)b;
    if (x->src_node != y->src_node) {
        return x->src_node < y->src_node ? -1 : 1;
    }
    return (x->dst_node > y->dst_node) - (x->dst_node < y->dst_node);
}

// Hybrid LSD radix and quicksort routine for pair queues.
static GrB_Info cfl_sort_pair_queue(CFL_PairQueue *q, CFL_PairQueue *tmp) {
    size_t n = q->n;
    if (n <= 1) {
        return GrB_SUCCESS;
    }
    if (n < SORT_SMALL) {
        qsort(q->v, n, sizeof(CFL_VertexPair), cfl_compare_vertex_pairs);
        return GrB_SUCCESS;
    }

    GrB_Index or_src = 0, and_src = ~(GrB_Index)0;
    GrB_Index or_dst = 0, and_dst = ~(GrB_Index)0;
    for (size_t k = 0; k < n; k++) {
        or_src |= q->v[k].src_node;
        and_src &= q->v[k].src_node;
        or_dst |= q->v[k].dst_node;
        and_dst &= q->v[k].dst_node;
    }

    GrB_Index diff[2] = {or_dst ^ and_dst,
                         or_src ^ and_src}; // 0 = dst_node, 1 = src_node
    if (tmp->cap < n) {
        CFL_VertexPair *p = realloc(tmp->v, n * sizeof(CFL_VertexPair));
        if (!p) {
            return GrB_OUT_OF_MEMORY;
        }
        tmp->v = p;
        tmp->cap = n;
    }

    CFL_VertexPair *src = q->v;
    CFL_VertexPair *dst = tmp->v;

    for (int pass = 0; pass < 2; pass++) {
        const bool sortBySrc = (pass == 1);
        GrB_Index diff_bit = diff[pass];
        if (diff_bit == 0) {
            continue;
        }

        unsigned shifts[64 / RADIX_BITS + 1];
        size_t num_shifts = 0;
        for (unsigned sh = 0; sh < 64; sh += RADIX_BITS) {
            if (((diff_bit >> sh) & (RADIX_SIZE - 1)) != 0) {
                shifts[num_shifts++] = sh;
            }
        }
        if (num_shifts == 0) {
            continue;
        }

        size_t hist[num_shifts][RADIX_SIZE];
        memset(hist, 0, num_shifts * RADIX_SIZE * sizeof(size_t));

        for (size_t k = 0; k < n; k++) {
            GrB_Index val = sortBySrc ? src[k].src_node : src[k].dst_node;
            for (size_t s = 0; s < num_shifts; s++) {
                hist[s][(val >> shifts[s]) & (RADIX_SIZE - 1)]++;
            }
        }

        for (size_t s = 0; s < num_shifts; s++) {
            unsigned sh = shifts[s];
            size_t *cnt = hist[s];

            size_t sum = 0;
            for (unsigned b = 0; b < RADIX_SIZE; b++) {
                size_t c = cnt[b];
                cnt[b] = sum;
                sum += c;
            }

            for (size_t k = 0; k < n; k++) {
                GrB_Index val = sortBySrc ? src[k].src_node : src[k].dst_node;
                dst[cnt[(val >> sh) & (RADIX_SIZE - 1)]++] = src[k];
            }

            CFL_VertexPair *temp = src;
            src = dst;
            dst = temp;
        }
    }

    if (src != q->v) {
        CFL_VertexPair *tmp_p = q->v;
        size_t tmp_c = q->cap;

        q->v = tmp->v;
        q->cap = tmp->cap;

        tmp->v = tmp_p;
        tmp->cap = tmp_c;
    }
    return GrB_SUCCESS;
}

static GrB_Info cfl_frontier_init(CFL_Frontier *F, size_t symbols_amount) {
    memset(F, 0, sizeof(*F));
    F->q = calloc(symbols_amount, sizeof(CFL_PairQueue));
    F->active = malloc(symbols_amount * sizeof(int32_t));
    if (!F->q || !F->active) {
        free(F->q);
        free(F->active);
        memset(F, 0, sizeof(*F));
        return GrB_OUT_OF_MEMORY;
    }
    return GrB_SUCCESS;
}

static void cfl_frontier_free(CFL_Frontier *F, size_t symbols_amount) {
    if (!F)
        return;
    if (F->q) {
        for (size_t a = 0; a < symbols_amount; a++) {
            free(F->q[a].v);
        }
        free(F->q);
    }
    free(F->active);
    memset(F, 0, sizeof(*F));
}

static GrB_Info paths_view_close(PathsView *v) {
    if (!v || !v->open) {
        return GrB_SUCCESS;
    }
    GrB_Info info = GxB_Matrix_pack_HyperCSR(
        v->mat, &v->Ap, &v->Ah, &v->Aj, (void **)&v->Ax, v->Ap_size, v->Ah_size,
        v->Aj_size, v->Ax_size, v->iso, v->nvec, false, NULL);
    free(v->visited);
    free(v->bstart);
    memset(v, 0, sizeof(*v));
    return info;
}

// Builds a bucket index for rapid row lookup inside sparse matrices.
static GrB_Info paths_view_build_buckets(PathsView *v, GrB_Index n) {
    if (v->nvec < 32 || v->nvec > UINT32_MAX) {
        return GrB_SUCCESS;
    }

    size_t base = ((size_t)v->nvec * 2 + v->nnz) * sizeof(GrB_Index);
    GrB_Index max_nb = (GrB_Index)(base / BUCKET_MEM_BUDGET_DIVISOR / sizeof(uint32_t));
    if (max_nb < v->nvec) {
        max_nb = v->nvec;
    }

    uint32_t shift = 0;
    while (((n >> shift) + 1) > max_nb) {
        shift++;
    }

    GrB_Index nb = (n >> shift) + 1;
    v->bstart = malloc((nb + 1) * sizeof(uint32_t));
    if (!v->bstart) {
        return GrB_OUT_OF_MEMORY;
    }

    v->shift = shift;
    v->nbuckets = nb;

    GrB_Index m = 0;
    for (GrB_Index b = 0; b <= nb; b++) {
        while (m < v->nvec && (v->Ah[m] >> shift) < b) {
            m++;
        }
        v->bstart[b] = (uint32_t)m;
    }

    return GrB_SUCCESS;
}

static GrB_Info paths_view_open(PathsView *v, GrB_Matrix mat, GrB_Index n,
                                bool make_visited) {
    GrB_Info info = GrB_SUCCESS;
    memset(v, 0, sizeof(*v));
    if (!mat) {
        return GrB_SUCCESS;
    }

    v->mat = mat;
    info = GrB_Matrix_wait(mat, GrB_MATERIALIZE);
    if (info != GrB_SUCCESS) {
        return info;
    }

    info = GxB_Matrix_unpack_HyperCSR(mat, &v->Ap, &v->Ah, &v->Aj, (void **)&v->Ax,
                                      &v->Ap_size, &v->Ah_size, &v->Aj_size, &v->Ax_size,
                                      &v->iso, &v->nvec, NULL, NULL);
    if (info != GrB_SUCCESS) {
        return info;
    }

    v->open = true;
    v->nnz = (v->Ap && v->nvec) ? v->Ap[v->nvec] : 0;

    if (make_visited && v->nnz > 0) {
        v->visited = calloc((size_t)((v->nnz + 63) / 64), sizeof(uint64_t));
        if (!v->visited) {
            paths_view_close(v);
            return GrB_OUT_OF_MEMORY;
        }
    }

    info = paths_view_build_buckets(v, n);
    if (info != GrB_SUCCESS) {
        paths_view_close(v);
        return info;
    }

    return GrB_SUCCESS;
}

static inline bool paths_view_find_row_range(const PathsView *v, GrB_Index row_idx,
                                             GrB_Index *out_start, GrB_Index *out_end) {
    if (!v->open || v->nvec == 0) {
        return false;
    }

    GrB_Index lo, hi;
    if (v->bstart) {
        GrB_Index b = row_idx >> v->shift;
        if (b >= v->nbuckets) {
            return false;
        }
        lo = v->bstart[b];
        hi = v->bstart[b + 1];
        if (lo == hi) {
            return false;
        }
        if (v->shift == 0) {
            goto have_row;
        }
    } else {
        lo = 0;
        hi = v->nvec;
    }

    while (hi - lo > BINARY_SEARCH_THRESHOLD) {
        GrB_Index m = lo + (hi - lo) / 2;
        if (v->Ah[m] < row_idx) {
            lo = m + 1;
        } else {
            hi = m;
        }
    }
    while (lo < hi && v->Ah[lo] < row_idx) {
        lo++;
    }

    if (lo >= v->nvec || v->Ah[lo] != row_idx) {
        return false;
    }

have_row:
    if (out_start) {
        *out_start = v->Ap[lo];
    }
    if (out_end) {
        *out_end = v->Ap[lo + 1];
    }
    return true;
}

static inline bool paths_view_find_col_in_range(const PathsView *v, GrB_Index start,
                                                GrB_Index end, GrB_Index col_idx,
                                                GrB_Index *out_idx) {
    GrB_Index e = end;
    while (end - start > BINARY_SEARCH_THRESHOLD) {
        GrB_Index m = start + (end - start) / 2;
        if (v->Aj[m] < col_idx) {
            start = m + 1;
        } else {
            end = m;
        }
    }
    while (start < end && v->Aj[start] < col_idx) {
        start++;
    }

    if (start < e && v->Aj[start] == col_idx) {
        if (out_idx) {
            *out_idx = start;
        }
        return true;
    }
    return false;
}

static inline bool paths_view_find_elem(const PathsView *v, GrB_Index row_idx,
                                        GrB_Index col_idx, GrB_Index *out_idx) {
    GrB_Index start, end;
    if (!paths_view_find_row_range(v, row_idx, &start, &end)) {
        return false;
    }
    return paths_view_find_col_in_range(v, start, end, col_idx, out_idx);
}

static inline bool cfl_bit_test_and_set(uint64_t *visited, GrB_Index p) {
    uint64_t m = UINT64_C(1) << (p & 63);
    bool old = (visited[p >> 6] & m) != 0;
    visited[p >> 6] |= m;
    return old;
}

// Claims a pair (i, j) for symbol processing if not previously visited.
static inline GrB_Info cfl_frontier_claim_pair(PathsView *fast_paths, int32_t A,
                                               GrB_Index i, GrB_Index j, GrB_Index pos,
                                               CFL_Frontier *F) {
    PathsView *v = &fast_paths[A];
    if (!v->open || pos >= v->nnz || !v->visited) {
        return GrB_INVALID_INDEX;
    }
    if (cfl_bit_test_and_set(v->visited, pos)) {
        return GrB_SUCCESS;
    }

    CFL_PairQueue *queue = &F->q[A];
    if (queue->n == 0) {
        F->active[F->active_count++] = A;
    }
    return cfl_pair_queue_push(queue, (CFL_VertexPair){i, j});
}

static GrB_Info init_row_presence(RowPresence *rp, const PathsView *fast_paths,
                                  size_t symbols_amount, GrB_Index n) {
    memset(rp, 0, sizeof(*rp));
    if (symbols_amount == 0 || n == 0) {
        return GrB_SUCCESS;
    }

    rp->words = (symbols_amount + 63) / 64;
    rp->bits = calloc((size_t)n * rp->words, sizeof(uint64_t));
    if (!rp->bits) {
        return GrB_OUT_OF_MEMORY;
    }

    for (size_t a = 0; a < symbols_amount; a++) {
        const PathsView *v = &fast_paths[a];
        if (!v->open || v->nvec == 0) {
            continue;
        }

        size_t word_offset = a >> 6;
        uint64_t mask = UINT64_C(1) << (a & 63);

        for (GrB_Index h = 0; h < v->nvec; h++) {
            GrB_Index row = v->Ah[h];
            if (row < n) {
                rp->bits[(size_t)row * rp->words + word_offset] |= mask;
            }
        }
    }

    return GrB_SUCCESS;
}

static inline bool row_presence_has(const RowPresence *rp, int32_t symbol,
                                    GrB_Index row) {
    if (!rp->bits) {
        return true;
    }
    size_t word_offset = (size_t)symbol >> 6;
    uint64_t mask = UINT64_C(1) << (symbol & 63);
    return (rp->bits[(size_t)row * rp->words + word_offset] & mask) != 0;
}

static void free_row_presence(RowPresence *rp) {
    if (!rp) {
        return;
    }
    free(rp->bits);
    memset(rp, 0, sizeof(*rp));
}

static int cfl_compare_binary_rules(const void *pa, const void *pb) {
    const BinRule *a = pa;
    const BinRule *b = pb;
    if (a->B != b->B) {
        return a->B < b->B ? -1 : 1;
    }
    if (a->C != b->C) {
        return a->C < b->C ? -1 : 1;
    }
    return 0;
}

static GrB_Info build_binary_index(BinaryIndex *bi, const CFL_triple *triples,
                                   size_t triples_count, size_t symbols_amount) {
    memset(bi, 0, sizeof(*bi));
    bi->offset = calloc(symbols_amount + 1, sizeof(size_t));
    if (!bi->offset) {
        return GrB_OUT_OF_MEMORY;
    }

    for (size_t z = 0; z < triples_count; z++) {
        int32_t A = triples[z].A;
        if (A >= 0 && (size_t)A < symbols_amount) {
            bi->offset[(size_t)A + 1]++;
        }
    }

    for (size_t a = 0; a < symbols_amount; a++) {
        bi->offset[a + 1] += bi->offset[a];
    }

    size_t total = bi->offset[symbols_amount];
    bi->rules = malloc((total ? total : 1) * sizeof(BinRule));
    if (!bi->rules) {
        free(bi->offset);
        bi->offset = NULL;
        return GrB_OUT_OF_MEMORY;
    }

    size_t *cursor = malloc((symbols_amount ? symbols_amount : 1) * sizeof(size_t));
    if (!cursor) {
        free(bi->rules);
        free(bi->offset);
        memset(bi, 0, sizeof(*bi));
        return GrB_OUT_OF_MEMORY;
    }
    memcpy(cursor, bi->offset, symbols_amount * sizeof(size_t));

    for (size_t z = 0; z < triples_count; z++) {
        int32_t A = triples[z].A;
        if (A >= 0 && (size_t)A < symbols_amount) {
            bi->rules[cursor[A]++] = (BinRule){triples[z].B, triples[z].C};
        }
    }
    free(cursor);

    size_t write_pos = 0;
    for (size_t a = 0; a < symbols_amount; a++) {
        size_t start = bi->offset[a];
        size_t count = bi->offset[a + 1] - start;
        bi->offset[a] = write_pos;

        if (count > 0) {
            qsort(&bi->rules[start], count, sizeof(BinRule), cfl_compare_binary_rules);

            bi->rules[write_pos++] = bi->rules[start];
            for (size_t i = 1; i < count; i++) {
                if (bi->rules[start + i].B != bi->rules[write_pos - 1].B ||
                    bi->rules[start + i].C != bi->rules[write_pos - 1].C) {
                    bi->rules[write_pos++] = bi->rules[start + i];
                }
            }
        }
    }
    bi->offset[symbols_amount] = write_pos;

    return GrB_SUCCESS;
}

static void free_binary_index(BinaryIndex *bi) {
    if (!bi) {
        return;
    }
    free(bi->rules);
    free(bi->offset);
    memset(bi, 0, sizeof(*bi));
}

static int compare_term_rules(const void *pa, const void *pb) {
    const TermRule *a = pa;
    const TermRule *b = pb;
    return (a->a > b->a) - (a->a < b->a);
}

static GrB_Info build_term_index(TermIndex *ti, const CFL_TermRule *terminal_rules,
                                 size_t terminal_count, size_t symbols_amount) {
    memset(ti, 0, sizeof(*ti));
    ti->offset = calloc(symbols_amount + 1, sizeof(size_t));
    if (!ti->offset) {
        return GrB_OUT_OF_MEMORY;
    }

    for (size_t z = 0; z < terminal_count; z++) {
        int32_t A = terminal_rules[z].A;
        if (A >= 0 && (size_t)A < symbols_amount) {
            ti->offset[(size_t)A + 1]++;
        }
    }

    for (size_t a = 0; a < symbols_amount; a++) {
        ti->offset[a + 1] += ti->offset[a];
    }

    size_t total = ti->offset[symbols_amount];
    ti->rules = malloc((total ? total : 1) * sizeof(TermRule));
    if (!ti->rules) {
        free(ti->offset);
        ti->offset = NULL;
        return GrB_OUT_OF_MEMORY;
    }

    size_t *cursor = malloc((symbols_amount ? symbols_amount : 1) * sizeof(size_t));
    if (!cursor) {
        free(ti->rules);
        free(ti->offset);
        memset(ti, 0, sizeof(*ti));
        return GrB_OUT_OF_MEMORY;
    }
    memcpy(cursor, ti->offset, symbols_amount * sizeof(size_t));

    for (size_t z = 0; z < terminal_count; z++) {
        int32_t A = terminal_rules[z].A;
        if (A >= 0 && (size_t)A < symbols_amount) {
            ti->rules[cursor[A]++] = (TermRule){terminal_rules[z].a};
        }
    }
    free(cursor);

    size_t write_pos = 0;
    for (size_t a = 0; a < symbols_amount; a++) {
        size_t start = ti->offset[a];
        size_t count = ti->offset[a + 1] - start;
        ti->offset[a] = write_pos;

        if (count > 0) {
            qsort(&ti->rules[start], count, sizeof(TermRule), compare_term_rules);

            ti->rules[write_pos++] = ti->rules[start];
            for (size_t i = 1; i < count; i++) {
                if (ti->rules[start + i].a != ti->rules[write_pos - 1].a) {
                    ti->rules[write_pos++] = ti->rules[start + i];
                }
            }
        }
    }
    ti->offset[symbols_amount] = write_pos;

    return GrB_SUCCESS;
}

static void free_term_index(TermIndex *ti) {
    if (!ti) {
        return;
    }
    free(ti->rules);
    free(ti->offset);
    memset(ti, 0, sizeof(*ti));
}

static GrB_Info cfl_edge_append(CFL_EdgeBuffer *b, GrB_Index i, GrB_Index j) {
    if (b->n == b->cap) {
        size_t nc = cfl_grow_capacity(b->cap, b->n + 1);
        if (nc < b->cap || nc > SIZE_MAX / sizeof(GrB_Index)) {
            return GrB_OUT_OF_MEMORY;
        }
        GrB_Index *ni = realloc(b->rows, nc * sizeof(GrB_Index));
        if (!ni) {
            return GrB_OUT_OF_MEMORY;
        }
        b->rows = ni;

        GrB_Index *nj = realloc(b->cols, nc * sizeof(GrB_Index));
        if (!nj) {
            return GrB_OUT_OF_MEMORY;
        }
        b->cols = nj;
        b->cap = nc;
    }
    b->rows[b->n] = i;
    b->cols[b->n] = j;
    b->n++;
    return GrB_SUCCESS;
}

static GrB_Info cfl_build_edge_matrix(GrB_Matrix *out, GrB_Index n,
                                      const CFL_EdgeBuffer *b) {
    GrB_Info info;
    bool *bool_values = NULL;
    if (b->n == 0) {
        return GrB_SUCCESS;
    }

    bool_values = malloc(b->n * sizeof(bool));
    if (!bool_values) {
        return GrB_OUT_OF_MEMORY;
    }
    memset(bool_values, 1, b->n * sizeof(bool));

    info = GrB_Matrix_new(out, GrB_BOOL, n, n);
    if (info == GrB_SUCCESS) {
        info = GrB_Matrix_build_BOOL(*out, b->rows, b->cols, bool_values, (GrB_Index)b->n,
                                     GrB_LOR);
    }
    free(bool_values);
    return info;
}

// Core worklist algorithm performing BFS level processing, gallop-based joins, and rule
// evaluations.
static GrB_Info extract_edges_worklist(GrB_Matrix *edges, const GrB_Matrix *R,
                                       const GrB_Matrix *adj_matrices,
                                       size_t symbols_amount, GrB_Index n,
                                       size_t start_nonterm, const CFL_triple *triples,
                                       size_t triples_count,
                                       const CFL_TermRule *terminal_rules,
                                       size_t terminal_count, GrB_Matrix pairs) {
    GrB_Info info = GrB_SUCCESS;
    PathsView *fast_paths = NULL;
    PathsView *adj_views = NULL;
    CFL_EdgeBuffer *eb = NULL;
    RowPresence rp = {0};
    BinaryIndex bin_idx = {0};
    TermIndex term_idx = {0};
    CFL_Frontier cur = {0}, next = {0};
    CFL_PairQueue tmp_sort_queue = {0};
    GrB_Index *target_cols_buffer = NULL;
    size_t target_cols_cap = 0;
    GrB_Index *pair_rows = NULL, *pair_cols = NULL;
    bool *pair_vals = NULL;
    GrB_Index nz = 0;

    if (!edges || !R || !adj_matrices || start_nonterm >= symbols_amount) {
        return GrB_NULL_POINTER;
    }

    fast_paths = calloc(symbols_amount, sizeof(*fast_paths));
    adj_views = calloc(symbols_amount, sizeof(*adj_views));
    eb = calloc(symbols_amount, sizeof(*eb));
    if (!fast_paths || !adj_views || !eb) {
        info = GrB_OUT_OF_MEMORY;
        goto cleanup;
    }

    info = cfl_frontier_init(&cur, symbols_amount);
    if (info != GrB_SUCCESS) {
        goto cleanup;
    }

    info = cfl_frontier_init(&next, symbols_amount);
    if (info != GrB_SUCCESS) {
        goto cleanup;
    }

    info = build_binary_index(&bin_idx, triples, triples_count, symbols_amount);
    if (info != GrB_SUCCESS) {
        goto cleanup;
    }

    info = build_term_index(&term_idx, terminal_rules, terminal_count, symbols_amount);
    if (info != GrB_SUCCESS) {
        goto cleanup;
    }

    for (size_t a = 0; a < symbols_amount; a++) {
        if (R[a]) {
            info = paths_view_open(&fast_paths[a], R[a], n, true);
            if (info != GrB_SUCCESS) {
                goto cleanup;
            }
        }
    }

    for (size_t a = 0; a < symbols_amount; a++) {
        if (adj_matrices[a]) {
            info = paths_view_open(&adj_views[a], adj_matrices[a], n, false);
            if (info != GrB_SUCCESS) {
                goto cleanup;
            }
        }
    }

    info = init_row_presence(&rp, fast_paths, symbols_amount, n);
    if (info != GrB_SUCCESS) {
        goto cleanup;
    }

    // Initialization of starting states for the BFS frontier
    if (pairs == NULL) {
        PathsView *s = &fast_paths[start_nonterm];
        if (s->open) {
            for (GrB_Index h = 0; h < s->nvec; h++) {
                GrB_Index i = s->Ah[h];
                for (GrB_Index pos = s->Ap[h]; pos < s->Ap[h + 1]; pos++) {
                    GrB_Index j = s->Aj[pos];
                    if (i == j) {
                        continue;
                    }
                    info = cfl_frontier_claim_pair(fast_paths, (int32_t)start_nonterm, i,
                                                   j, pos, &cur);
                    if (info != GrB_SUCCESS) {
                        goto cleanup;
                    }
                }
            }
        }
    } else {
        info = GrB_Matrix_nvals(&nz, pairs);
        if (info != GrB_SUCCESS) {
            goto cleanup;
        }

        pair_rows = malloc((size_t)(nz ? nz : 1) * sizeof(GrB_Index));
        pair_cols = malloc((size_t)(nz ? nz : 1) * sizeof(GrB_Index));
        pair_vals = malloc((size_t)(nz ? nz : 1) * sizeof(bool));
        if (!pair_rows || !pair_cols || !pair_vals) {
            info = GrB_OUT_OF_MEMORY;
            goto cleanup;
        }

        info = GrB_Matrix_extractTuples_BOOL(pair_rows, pair_cols, pair_vals, &nz, pairs);
        if (info != GrB_SUCCESS) {
            goto cleanup;
        }

        PathsView *s = &fast_paths[start_nonterm];
        for (GrB_Index z = 0; z < nz; z++) {
            if (pair_vals[z] && pair_rows[z] < n && pair_cols[z] < n) {
                GrB_Index pos;
                if (paths_view_find_elem(s, pair_rows[z], pair_cols[z], &pos)) {
                    info = cfl_frontier_claim_pair(fast_paths, (int32_t)start_nonterm,
                                                   pair_rows[z], pair_cols[z], pos, &cur);
                    if (info != GrB_SUCCESS) {
                        goto cleanup;
                    }
                }
            }
        }
    }

    // Level-by-level processing of the frontier (BFS loop)
    while (cur.active_count > 0) {
        for (size_t a = 0; a < cur.active_count; a++) {
            int32_t A = cur.active[a];
            CFL_PairQueue *qa = &cur.q[A];

            info = cfl_sort_pair_queue(qa, &tmp_sort_queue);
            if (info != GrB_SUCCESS) {
                goto cleanup;
            }

            for (size_t idx = 0; idx < qa->n;) {
                GrB_Index i = qa->v[idx].src_node;
                size_t end = idx;
                while (end < qa->n && qa->v[end].src_node == i) {
                    end++;
                }

                size_t m = end - idx;
                if (m > target_cols_cap) {
                    size_t ncap = cfl_grow_capacity(target_cols_cap, m);
                    GrB_Index *njs =
                        realloc(target_cols_buffer, ncap * sizeof(GrB_Index));
                    if (!njs) {
                        info = GrB_OUT_OF_MEMORY;
                        goto cleanup;
                    }
                    target_cols_buffer = njs;
                    target_cols_cap = ncap;
                }

                for (size_t k = 0; k < m; k++) {
                    target_cols_buffer[k] = qa->v[idx + k].dst_node;
                }

                // 1. Terminal rules processing for group (A, i) using galloping
                // intersection
                size_t t_begin = term_idx.offset[A];
                size_t t_end = term_idx.offset[A + 1];
                for (size_t z = t_begin; z < t_end; z++) {
                    int32_t a_sym = term_idx.rules[z].a;
                    PathsView *vTerm = &adj_views[a_sym];
                    GrB_Index lTerm, hTerm;
                    if (paths_view_find_row_range(vTerm, i, &lTerm, &hTerm)) {
                        size_t a_idx = 0;
                        GrB_Index q = lTerm;
                        const GrB_Index *Aj_term = vTerm->Aj;
                        while (a_idx < m && q < hTerm) {
                            if (target_cols_buffer[a_idx] < Aj_term[q]) {
                                a_idx = cfl_gallop_search(target_cols_buffer, a_idx, m,
                                                          Aj_term[q]);
                            } else if (Aj_term[q] < target_cols_buffer[a_idx]) {
                                q = cfl_gallop_search(Aj_term, q, hTerm,
                                                      target_cols_buffer[a_idx]);
                            } else {
                                info = cfl_edge_append(&eb[a_sym], i,
                                                       target_cols_buffer[a_idx]);
                                if (info != GrB_SUCCESS) {
                                    goto cleanup;
                                }
                                a_idx++;
                                q++;
                            }
                        }
                    }
                }

                // 2. Binary non-terminal rules processing for group (A, i)
                size_t r_begin = bin_idx.offset[A];
                size_t r_end = bin_idx.offset[A + 1];
                size_t r = r_begin;

                while (r < r_end) {
                    int32_t B = bin_idx.rules[r].B;
                    size_t r_b_end = r + 1;
                    while (r_b_end < r_end && bin_idx.rules[r_b_end].B == B) {
                        r_b_end++;
                    }

                    if (row_presence_has(&rp, B, i)) {
                        PathsView *vB = &fast_paths[B];
                        GrB_Index lB, hB;
                        if (paths_view_find_row_range(vB, i, &lB, &hB)) {
                            for (GrB_Index pB = lB; pB < hB; pB++) {
                                GrB_Index k = vB->Aj[pB];
                                bool hitB = false;

                                for (size_t sub_r = r; sub_r < r_b_end; sub_r++) {
                                    int32_t C = bin_idx.rules[sub_r].C;
                                    PathsView *vC = &fast_paths[C];
                                    GrB_Index lC, hC;
                                    if (!paths_view_find_row_range(vC, k, &lC, &hC)) {
                                        continue;
                                    }

                                    size_t a_idx = 0;
                                    GrB_Index q = lC;
                                    const GrB_Index *Aj_C = vC->Aj;

                                    while (a_idx < m && q < hC) {
                                        if (target_cols_buffer[a_idx] < Aj_C[q]) {
                                            a_idx = cfl_gallop_search(target_cols_buffer,
                                                                      a_idx, m, Aj_C[q]);
                                        } else if (Aj_C[q] < target_cols_buffer[a_idx]) {
                                            q = cfl_gallop_search(
                                                Aj_C, q, hC, target_cols_buffer[a_idx]);
                                        } else {
                                            info = cfl_frontier_claim_pair(
                                                fast_paths, C, k,
                                                target_cols_buffer[a_idx], q, &next);
                                            if (info != GrB_SUCCESS) {
                                                goto cleanup;
                                            }
                                            hitB = true;
                                            a_idx++;
                                            q++;
                                        }
                                    }
                                }

                                if (hitB) {
                                    info = cfl_frontier_claim_pair(fast_paths, B, i, k,
                                                                   pB, &next);
                                    if (info != GrB_SUCCESS) {
                                        goto cleanup;
                                    }
                                }
                            }
                        }
                    }
                    r = r_b_end;
                }

                idx = end;
            }
            qa->n = 0;
        }

        cur.active_count = 0;
        CFL_Frontier t = cur;
        cur = next;
        next = t;
    }

    // Assemble final output matrices
    for (size_t a = 0; a < symbols_amount; a++) {
        if (eb[a].n) {
            info = cfl_build_edge_matrix(&edges[a], n, &eb[a]);
            if (info != GrB_SUCCESS) {
                goto cleanup;
            }

            info = GrB_Matrix_wait(edges[a], GrB_MATERIALIZE);
            if (info != GrB_SUCCESS) {
                goto cleanup;
            }
        }
    }

cleanup:
    if (fast_paths) {
        for (size_t a = 0; a < symbols_amount; a++) {
            paths_view_close(&fast_paths[a]);
        }
        free(fast_paths);
    }
    if (adj_views) {
        for (size_t a = 0; a < symbols_amount; a++) {
            paths_view_close(&adj_views[a]);
        }
        free(adj_views);
    }
    if (eb) {
        for (size_t a = 0; a < symbols_amount; a++) {
            free(eb[a].rows);
            free(eb[a].cols);
        }
        free(eb);
    }
    free_row_presence(&rp);
    free_binary_index(&bin_idx);
    free_term_index(&term_idx);
    cfl_frontier_free(&cur, symbols_amount);
    cfl_frontier_free(&next, symbols_amount);
    free(tmp_sort_queue.v);
    free(target_cols_buffer);
    free(pair_rows);
    free(pair_cols);
    free(pair_vals);

    return info;
}

// Main entry point for advanced Context-Free Language edge extraction.
GrB_Info LAGraph_CFL_Edges_adv(GrB_Matrix *edges, GrB_Matrix *reachability,
                               const GrB_Matrix *adj_matrices, size_t symbols_amount,
                               const LAGraph_rule_EWCNF *rules, size_t rules_count,
                               size_t start_nonterm, const GrB_Matrix pairs, char *msg,
                               int8_t optimizations) {
    LG_CLEAR_MSG;
    GrB_Info info = GrB_SUCCESS;

    GrB_Matrix *R = NULL;
    LAGraph_rule_EWCNF *new_rules = NULL;
    size_t new_rules_count = 0;
    CFL_triple *triples = NULL;
    size_t triples_count = 0, triples_cap = 0;
    CFL_TermRule *terminal_rules = NULL;
    size_t terminal_count = 0;
    GrB_Scalar thunk_zero = NULL;
    GrB_Index n = 0;

    LG_ASSERT_MSG(edges != NULL, GrB_NULL_POINTER, "The edges array cannot be null.");
    LG_ASSERT_MSG(adj_matrices != NULL, GrB_NULL_POINTER,
                  "The adjacency matrices array cannot be null.");
    LG_ASSERT_MSG(rules != NULL || rules_count == 0, GrB_NULL_POINTER,
                  "The rules array cannot be null.");
    LG_ASSERT_MSG(start_nonterm < symbols_amount, GrB_INVALID_INDEX,
                  "Invalid start nonterminal.");

    for (size_t i = 0; i < symbols_amount; i++) {
        edges[i] = NULL;
    }
    if (reachability != NULL) {
        *reachability = NULL;
    }

    LG_TRY(LAGraph_Calloc((void **)&R, symbols_amount, sizeof(GrB_Matrix), msg));
    LG_TRY(LAGraph_CFL_reachability_adv(R, adj_matrices, symbols_amount, rules,
                                        rules_count, msg, optimizations));

    if (R[start_nonterm] == NULL) {
        goto cleanup;
    }

    for (size_t i = 0; i < symbols_amount; i++) {
        if (adj_matrices[i] != NULL) {
            GRB_TRY(GrB_Matrix_ncols(&n, adj_matrices[i]));
            break;
        }
    }
    if (n == 0) {
        GRB_TRY(GrB_Matrix_nrows(&n, R[start_nonterm]));
    }

    if (pairs != NULL) {
        GrB_Matrix intersection = NULL;
        GRB_TRY(GrB_Matrix_new(&intersection, GrB_BOOL, n, n));

        GRB_TRY(GrB_Matrix_eWiseMult_BinaryOp(intersection, NULL, NULL, GrB_LAND,
                                              R[start_nonterm], pairs, NULL));

        GrB_Index nz_common = 0;
        GRB_TRY(GrB_Matrix_nvals(&nz_common, intersection));
        GrB_free(&intersection);

        if (nz_common == 0) {
            goto cleanup;
        }
    }

    GRB_TRY(GrB_Scalar_new(&thunk_zero, GrB_INT64));
    GRB_TRY(GrB_Scalar_setElement_INT64(thunk_zero, 0));

    for (size_t i = 0; i < rules_count; i++) {
        new_rules_count += (rules[i].indexed_count == 0) ? 1 : rules[i].indexed_count;
    }
    LG_TRY(LAGraph_Calloc((void **)&new_rules, new_rules_count,
                          sizeof(LAGraph_rule_EWCNF), msg));

    size_t nr_idx = 0;
    for (size_t i = 0; i < rules_count; i++) {
        LAGraph_rule_EWCNF rule = rules[i];
        if (rule.indexed_count == 0) {
            new_rules[nr_idx++] = rule;
        } else {
            for (size_t rule_index = 0; rule_index < rule.indexed_count; rule_index++) {
                LAGraph_rule_EWCNF exploded_rule = rule;
                exploded_rule.indexed_count = 0;
                exploded_rule.indexed = 0;

                if (rule.nonterm != -1 && (rule.indexed & LAGraph_EWNCF_INDEX_NONTERM)) {
                    exploded_rule.nonterm = rule.nonterm + rule_index;
                }
                if (rule.prod_A != -1 && (rule.indexed & LAGraph_EWNCF_INDEX_PROD_A)) {
                    exploded_rule.prod_A = rule.prod_A + rule_index;
                }
                if (rule.prod_B != -1 && (rule.indexed & LAGraph_EWNCF_INDEX_PROD_B)) {
                    exploded_rule.prod_B = rule.prod_B + rule_index;
                }
                new_rules[nr_idx++] = exploded_rule;
            }
        }
    }

    for (size_t i = 0; i < new_rules_count; i++) {
        LAGraph_rule_EWCNF bin_rule = new_rules[i];
        if (!(bin_rule.prod_A != -1 && bin_rule.prod_B != -1)) {
            continue;
        }

        const LAGraph_rule_Pat *pat = bin_rule.pat;

        if (pat != NULL && pat->kind == LAGraph_PAT_CONV) {
            int64_t N = pat->masks;
            int64_t Rr = pat->states;
            int64_t K = pat->idx_count;

            if (pat->element == LAGraph_PAT_ALL_ELEMENTS) {
                for (int64_t m = 0; m < N; m++) {
                    for (int64_t im = 0; im < N; im++) {
                        for (int64_t qs = 0; qs < Rr; qs++) {
                            for (int64_t qm = 0; qm < Rr; qm++) {
                                for (int64_t qe = 0; qe < Rr; qe++) {
                                    for (int64_t k = 0; k < K; k++) {
                                        int32_t cur_A =
                                            pat_role_id(&pat->role[0], m, qs, qe, 0);
                                        int32_t cur_pA =
                                            pat_role_id(&pat->role[1], im, qs, qm, k);
                                        int32_t cur_pB =
                                            pat_role_id(&pat->role[2], m ^ im, qm, qe, 0);
                                        EMIT(cur_A, cur_pA, cur_pB);
                                    }
                                }
                            }
                        }
                    }
                }
            } else {
                int64_t el = pat->element;
                uint32_t st_count = pat->state ? pat->state->nnz : (uint32_t)Rr;

                for (int64_t m = 0; m < N; m++) {
                    for (uint32_t st = 0; st < st_count; st++) {
                        int64_t qs = pat->state ? pat->state->entries[st].row : st;
                        int64_t qmid = pat->state ? pat->state->entries[st].col : st;

                        for (int64_t qe = 0; qe < Rr; qe++) {
                            int32_t cur_A = pat_role_id(&pat->role[0], m, qs, qe, 0);
                            int32_t cur_pA = bin_rule.prod_A;
                            int32_t cur_pB =
                                pat_role_id(&pat->role[2], m ^ el, qmid, qe, 0);
                            EMIT(cur_A, cur_pA, cur_pB);
                        }
                    }
                }
            }
            continue;
        }

        if (pat != NULL && pat->kind == LAGraph_PAT_SCALE) {
            int64_t N = pat->masks;
            int64_t Rr = pat->states;

            for (int64_t m = 0; m < N; m++) {
                for (int64_t qs = 0; qs < Rr; qs++) {
                    for (int64_t qe = 0; qe < Rr; qe++) {
                        int32_t cur_A = pat_role_id(&pat->role[0], m, qs, qe, 0);
                        int32_t cur_pA = bin_rule.prod_A;
                        int32_t cur_pB = pat_role_id(&pat->role[2], m, qs, qe, 0);
                        EMIT(cur_A, cur_pA, cur_pB);
                    }
                }
            }
            continue;
        }

        if (pat != NULL &&
            (pat->kind == LAGraph_PAT_LEFT || pat->kind == LAGraph_PAT_RIGHT)) {
            int64_t N = pat->masks;
            int64_t Rr = pat->states;
            int64_t off = bin_rule.nonterm - pat->role[0].base;

            if (off < 0 || off >= (int64_t)pat->idx_count) {
                continue;
            }
            int64_t i_idx = off;

            for (int64_t im = 0; im < N; im++) {
                for (int64_t qs = 0; qs < Rr; qs++) {
                    for (int64_t qm = 0; qm < Rr; qm++) {
                        int32_t cur_A, cur_pA, cur_pB;

                        if (pat->kind == LAGraph_PAT_LEFT) {
                            cur_A = pat_role_id(&pat->role[0], im, qs, qm, i_idx);
                            cur_pA = bin_rule.prod_A;
                            cur_pB = pat_role_id(&pat->role[2], im, qs, qm, i_idx);
                        } else {
                            cur_A = pat_role_id(&pat->role[0], im, qs, qm, i_idx);
                            cur_pA = pat_role_id(&pat->role[1], im, qs, qm, 0);
                            cur_pB = bin_rule.prod_B;
                        }
                        EMIT(cur_A, cur_pA, cur_pB);
                    }
                }
            }
            continue;
        }

        EMIT(bin_rule.nonterm, bin_rule.prod_A, bin_rule.prod_B);
    }

    terminal_rules = calloc(new_rules_count ? new_rules_count : 1, sizeof(CFL_TermRule));
    if (terminal_rules == NULL) {
        info = GrB_OUT_OF_MEMORY;
        goto cleanup;
    }

    for (size_t i = 0; i < new_rules_count; i++) {
        LAGraph_rule_EWCNF rule = new_rules[i];
        if (rule.prod_A != -1 && rule.prod_B == -1 && rule.nonterm >= 0 &&
            rule.prod_A >= 0 && (size_t)rule.nonterm < symbols_amount &&
            (size_t)rule.prod_A < symbols_amount) {
            terminal_rules[terminal_count++] = (CFL_TermRule){rule.nonterm, rule.prod_A};
        }
    }

    if (reachability != NULL) {
        if (pairs == NULL) {
            GRB_TRY(GrB_Matrix_new(reachability, GrB_BOOL, n, n));
            GRB_TRY(GrB_select(*reachability, NULL, NULL, GrB_OFFDIAG, R[start_nonterm],
                               thunk_zero, NULL));
        } else {
            GRB_TRY(GrB_Matrix_new(reachability, GrB_BOOL, n, n));
            GRB_TRY(GrB_Matrix_eWiseMult_BinaryOp(*reachability, NULL, NULL, GrB_LAND,
                                                  R[start_nonterm], pairs, NULL));
        }
    }

    GRB_TRY(extract_edges_worklist(edges, R, adj_matrices, symbols_amount, n,
                                   start_nonterm, triples, triples_count, terminal_rules,
                                   terminal_count, pairs));

cleanup:
    GrB_free(&thunk_zero);
    free(terminal_rules);
    LG_FREE_WORK;
    if (info != GrB_SUCCESS && reachability != NULL) {
        GrB_free(reachability);
    }
    return info;
}
