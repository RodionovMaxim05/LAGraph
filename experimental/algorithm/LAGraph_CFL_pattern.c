//------------------------------------------------------------------------------
// LAGraph_CFL_Pat.c: OPT_PAT - block optimization of indexed pattern
//------------------------------------------------------------------------------

#include "LAGraph_CFL_pattern.h"
#include "LG_internal.h"
#include <LAGraphX.h>

#ifndef OPT_BLOCK
    #define OPT_BLOCK (1 << 3)
#endif

#define OPT_PAT (1 << 4) // requires OPT_BLOCK

typedef CFL_Matrix Matrix;

#define PAT_TRY(call)                                                                    \
    do {                                                                                 \
        info = (call);                                                                   \
        if (info < GrB_SUCCESS) {                                                        \
            fprintf(stderr, "LAGraph Pat failure (file %s, line %d): (%d)\n", __FILE__,  \
                    __LINE__, (int)info);                                                \
            goto done;                                                                   \
        }                                                                                \
    } while (0)

#define PAT_FAIL(status, ...)                                                            \
    do {                                                                                 \
        fprintf(stderr, "LAGraph Pat failure (file %s, line %d): ", __FILE__, __LINE__); \
        fprintf(stderr, __VA_ARGS__);                                                    \
        fprintf(stderr, "\n");                                                           \
        info = (status);                                                                 \
        goto done;                                                                       \
    } while (0)

//------------------------------------------------------------------------------
// Tuples utilities
//------------------------------------------------------------------------------

typedef struct {
    GrB_Index *r;
    GrB_Index *c;
    GrB_Index n;
} pat_tup;

static void tup_free(pat_tup *t) {
    LAGraph_Free((void **)&t->r, NULL);
    LAGraph_Free((void **)&t->c, NULL);
    t->n = 0;
}

static GrB_Info tup_alloc(pat_tup *t, GrB_Index cap) {
    t->r = NULL;
    t->c = NULL;
    t->n = 0;
    if (LAGraph_Malloc((void **)&t->r, cap, sizeof(GrB_Index), NULL) < 0 ||
        LAGraph_Malloc((void **)&t->c, cap, sizeof(GrB_Index), NULL) < 0) {
        tup_free(t);
        return GrB_OUT_OF_MEMORY;
    }
    return GrB_SUCCESS;
}

static GrB_Info tup_from_matrix(pat_tup *t, GrB_Matrix M) {
    GrB_Info info = GrB_SUCCESS;
    GrB_Index nv = 0;
    PAT_TRY(GrB_Matrix_nvals(&nv, M));
    PAT_TRY(tup_alloc(t, nv));
    GrB_Index cap = nv;
    PAT_TRY(GrB_Matrix_extractTuples_BOOL(t->r, t->c, NULL, &cap, M));
    t->n = cap;
done:
    if (info < GrB_SUCCESS) {
        tup_free(t);
    }
    return info;
}

static GrB_Info build_matrix(GrB_Matrix *out, const GrB_Index *r, const GrB_Index *c,
                             GrB_Index n, GrB_Index nrows, GrB_Index ncols) {
    GrB_Info info = GrB_SUCCESS;
    GrB_Scalar s = NULL;
    *out = NULL;
    PAT_TRY(GrB_Scalar_new(&s, GrB_BOOL));
    PAT_TRY(GrB_Scalar_setElement_BOOL(s, true));
    PAT_TRY(GrB_Matrix_new(out, GrB_BOOL, nrows, ncols));
    PAT_TRY(GxB_Matrix_build_Scalar(*out, r, c, s, n));
done:
    GrB_free(&s);
    if (info < GrB_SUCCESS) {
        GrB_free(out);
    }
    return info;
}

static GrB_Info tup_to_matrix(GrB_Matrix *out, const pat_tup *t, GrB_Index nrows,
                              GrB_Index ncols) {
    return build_matrix(out, t->r, t->c, t->n, nrows, ncols);
}

static GrB_Info pat_mxm(GrB_Matrix *out, GrB_Matrix A, GrB_Matrix B) {
    GrB_Info info = GrB_SUCCESS;
    GrB_Index nr, nc;
    *out = NULL;
    PAT_TRY(GrB_Matrix_nrows(&nr, A));
    PAT_TRY(GrB_Matrix_ncols(&nc, B));
    PAT_TRY(GrB_Matrix_new(out, GrB_BOOL, nr, nc));
    PAT_TRY(GrB_mxm(*out, GrB_NULL, GrB_NULL, GxB_ANY_PAIR_BOOL, A, B, GrB_NULL));
done:
    if (info < GrB_SUCCESS) {
        GrB_free(out);
    }
    return info;
}

//------------------------------------------------------------------------------
// Group law operations
//------------------------------------------------------------------------------

static inline GrB_Index pat_inv(LAGraph_Pat_group g, GrB_Index N, GrB_Index j, 
                               GrB_Index el) {
    if (g == LAGraph_PAT_GROUP_XOR) {
        return j ^ el;
    }
    return (j + N - (el % N)) % N;
}

static bool owner_nvals_of(const Matrix *owner, GrB_Index *nv) {
    if (owner == NULL || owner->is_lazy) {
        return false;
    }
    GrB_Info info = GrB_Matrix_nvals(nv, owner->base);
    return info >= GrB_SUCCESS;
}

//------------------------------------------------------------------------------
// Lifting of plain operands: X -> T (x) X
//------------------------------------------------------------------------------

typedef enum {
    LIFT_HORIZ, // Stack of lifted blocks, n' x (c n')
    LIFT_VERT,  // Stack of lifted blocks, (c n') x n'
    LIFT_SUM,   // Sum of all blocks, lifted: n' x n'
    LIFT_DIAG   // Block-diagonal of lifted blocks: (c n') x (c n')
} lift_mode;

static GrB_Info pat_lift(GrB_Matrix *out, GrB_Matrix in, GrB_Index n, uint32_t R,
                        const LAGraph_Pat_state_map *T, lift_mode mode) {
    GrB_Info info = GrB_SUCCESS;
    pat_tup src = {0}, dst = {0};
    GrB_Index nr, nc, np = n * R, count, d = 0;
    *out = NULL;

    PAT_TRY(GrB_Matrix_nrows(&nr, in));
    PAT_TRY(GrB_Matrix_ncols(&nc, in));
    bool vert = nr > nc;
    if (n == 0 || nr % n != 0 || nc % n != 0 || (nr != n && nc != n)) {
        PAT_FAIL(GrB_DIMENSION_MISMATCH,
                "plain operand %lux%lu is not a stack of %lux%lu blocks",
                (unsigned long)nr, (unsigned long)nc, (unsigned long)n,
                (unsigned long)n);
    }
    count = (vert ? nr : nc) / n;

    uint32_t nT = T ? T->nnz : R;
    PAT_TRY(tup_from_matrix(&src, in));
    PAT_TRY(tup_alloc(&dst, src.n * nT));

    for (GrB_Index i = 0; i < src.n; i++) {
        GrB_Index blk, x, y;
        if (vert) {
            blk = src.r[i] / n;
            x = src.r[i] % n;
            y = src.c[i];
        } else {
            blk = src.c[i] / n;
            x = src.r[i];
            y = src.c[i] % n;
        }
        for (uint32_t e = 0; e < nT; e++) {
            GrB_Index qr = T ? (GrB_Index)T->entries[e].row : e;
            GrB_Index qc = T ? (GrB_Index)T->entries[e].col : e;
            GrB_Index lr = qr * n + x, lc = qc * n + y;

            if (lr >= np || lc >= np) {
                fprintf(stderr,
                        "pat_lift OOB: lr=%lu lc=%lu np=%lu (qr=%lu qc=%lu x=%lu y=%lu blk=%lu)\n",
                        (unsigned long)lr, (unsigned long)lc, (unsigned long)np,
                        (unsigned long)qr, (unsigned long)qc, (unsigned long)x,
                        (unsigned long)y, (unsigned long)blk);
            }

            switch (mode) {
                case LIFT_HORIZ:
                    dst.r[d] = lr;
                    dst.c[d] = blk * np + lc;
                    break;
                case LIFT_VERT:
                    dst.r[d] = blk * np + lr;
                    dst.c[d] = lc;
                    break;
                case LIFT_SUM:
                    dst.r[d] = lr;
                    dst.c[d] = lc;
                    break;
                default:
                    dst.r[d] = blk * np + lr;
                    dst.c[d] = blk * np + lc;
                    break;
            }
            d++;
        }
    }
    dst.n = d;

    switch (mode) {
        case LIFT_HORIZ:
            PAT_TRY(tup_to_matrix(out, &dst, np, count * np));
            break;
        case LIFT_VERT:
            PAT_TRY(tup_to_matrix(out, &dst, count * np, np));
            break;
        case LIFT_SUM:
            PAT_TRY(tup_to_matrix(out, &dst, np, np));
            break;
        default:
            PAT_TRY(tup_to_matrix(out, &dst, count * np, count * np));
            break;
    }

done:
    tup_free(&src);
    tup_free(&dst);
    return info;
}

//------------------------------------------------------------------------------
// Re-layouts of the S stack and grids
//------------------------------------------------------------------------------

static GrB_Info pat_S_vert(GrB_Matrix *out, GrB_Matrix S, GrB_Index np, GrB_Index N) {
    GrB_Info info = GrB_SUCCESS;
    pat_tup t = {0};
    *out = NULL;
    PAT_TRY(tup_from_matrix(&t, S));
    for (GrB_Index i = 0; i < t.n; i++) {
        GrB_Index m = t.c[i] / np;
        t.r[i] = m * np + t.r[i];
        t.c[i] = t.c[i] % np;
    }
    PAT_TRY(tup_to_matrix(out, &t, N * np, np));
done:
    tup_free(&t);
    return info;
}

static GrB_Info pat_S_cayley(GrB_Matrix *out, GrB_Matrix S, GrB_Index np, GrB_Index N,
                            LAGraph_Pat_group g) {
    GrB_Info info = GrB_SUCCESS;
    pat_tup t = {0}, o = {0};
    *out = NULL;
    PAT_TRY(tup_from_matrix(&t, S));
    PAT_TRY(tup_alloc(&o, t.n * N));
    GrB_Index d = 0;
    for (GrB_Index i = 0; i < t.n; i++) {
        GrB_Index j = t.c[i] / np, cc = t.c[i] % np;
        for (GrB_Index im = 0; im < N; im++) {
            GrB_Index m = pat_inv(g, N, j, im);
            o.r[d] = im * np + t.r[i];
            o.c[d] = m * np + cc;
            d++;
        }
    }
    o.n = d;
    PAT_TRY(tup_to_matrix(out, &o, N * np, N * np));
done:
    tup_free(&t);
    tup_free(&o);
    return info;
}

static GrB_Info pat_make_fold_selector(GrB_Matrix *F, GrB_Index n, GrB_Index c,
                                      bool vert) {
    GrB_Info info = GrB_SUCCESS;
    GrB_Index nz = c * n;
    GrB_Index *r = NULL, *col = NULL;
    if (LAGraph_Malloc((void **)&r, nz, sizeof(GrB_Index), NULL) < 0 ||
        LAGraph_Malloc((void **)&col, nz, sizeof(GrB_Index), NULL) < 0) {
        LAGraph_Free((void **)&r, NULL);
        LAGraph_Free((void **)&col, NULL);
        return GrB_OUT_OF_MEMORY;
    }

    GrB_Index d = 0;
    if (vert) {
        // F: n x (c*n). Ensure r[d] is strictly increasing:
        for (GrB_Index i = 0; i < n; i++) {
            for (GrB_Index blk = 0; blk < c; blk++) {
                r[d] = i;
                col[d] = blk * n + i;
                d++;
            }
        }
        PAT_TRY(build_matrix(F, r, col, nz, n, c * n));
    } else {
        // F: (c*n) x n. Ensure r[d] is strictly increasing:
        for (GrB_Index blk = 0; blk < c; blk++) {
            for (GrB_Index i = 0; i < n; i++) {
                r[d] = blk * n + i;
                col[d] = i;
                d++;
            }
        }
        PAT_TRY(build_matrix(F, r, col, nz, c * n, n));
    }

done:
    LAGraph_Free((void **)&r, NULL);
    LAGraph_Free((void **)&col, NULL);
    return info;
}

static GrB_Info pat_fold_stack(GrB_Matrix *out, GrB_Matrix in, GrB_Index n,
                              const Pat_Context *ctx) {
    GrB_Info info = GrB_SUCCESS;
    GrB_Index nr, nc;
    PAT_TRY(GrB_Matrix_nrows(&nr, in));
    PAT_TRY(GrB_Matrix_ncols(&nc, in));

    if (nr == n && nc == n) {
        return GrB_Matrix_dup(out, in);
    }

    bool vert = nr > nc;
    GrB_Index c = (vert ? nr : nc) / n;
    GrB_Matrix F = NULL;

    // 1. Try to find a precomputed selector in the context cache
    if (ctx != NULL) {
        for (size_t i = 0; i < ctx->fold_cache_count; i++) {
            if (ctx->fold_cache[i].n == n && ctx->fold_cache[i].c == c &&
                ctx->fold_cache[i].vert == vert) {
                F = ctx->fold_cache[i].F;
                break;
            }
        }
    }

    // 2. If not found in cache, create and store it
    if (F == NULL) {
        GrB_Matrix new_F = NULL;
        PAT_TRY(pat_make_fold_selector(&new_F, n, c, vert));

        if (ctx != NULL) {
            Pat_Context *m_ctx = (Pat_Context *)ctx;

            // Expand cache capacity if necessary
            if (m_ctx->fold_cache_count >= m_ctx->fold_cache_cap) {
                size_t new_cap = m_ctx->fold_cache_cap ? m_ctx->fold_cache_cap * 2 : 4;
                pat_fold_cache_entry *p = realloc(m_ctx->fold_cache,
                                                 new_cap * sizeof(pat_fold_cache_entry));
                if (p == NULL) {
                    GrB_free(&new_F);
                    PAT_FAIL(GrB_OUT_OF_MEMORY, "pat_fold_stack: out of memory");
                }
                m_ctx->fold_cache = p;
                m_ctx->fold_cache_cap = new_cap;
            }
            m_ctx->fold_cache[m_ctx->fold_cache_count++] = (pat_fold_cache_entry){n, c, vert, new_F};
        }
        F = new_F;
    }

    if (vert) {
        PAT_TRY(pat_mxm(out, F, in));
    } else {
        PAT_TRY(pat_mxm(out, in, F));
    }

done:
    return info;
}

static GrB_Info pat_make_T_matrix(GrB_Matrix *T_out, const LAGraph_Pat_state_map *T, uint32_t R);

static GrB_Info pat_S_perm_fast(GrB_Matrix *out, GrB_Matrix S, const Pat_Context *ctx,
                               GrB_Index el, const Matrix *owner, bool *keep) {
    GrB_Info info = GrB_SUCCESS;
    *keep = false;
    GrB_Index nv = 0;
    bool cacheable = owner_nvals_of(owner, &nv);

    if (cacheable && ctx != NULL && el < ctx->N) {
        if (ctx->sp_cache[el].owner == owner && ctx->sp_cache[el].owner_nvals == nv &&
            ctx->sp_cache[el].Sp != NULL) {
            *out = ctx->sp_cache[el].Sp;
            *keep = true;
            return GrB_SUCCESS;
        }
    }

    PAT_TRY(pat_mxm(out, S, ctx->P_el[el]));

    if (cacheable && ctx != NULL && el < ctx->N) {
        Pat_Context *m_ctx = (Pat_Context *)ctx;
        if (m_ctx->sp_cache[el].Sp != NULL && m_ctx->sp_cache[el].Sp != *out) {
            GrB_free(&m_ctx->sp_cache[el].Sp);
        }
        m_ctx->sp_cache[el].owner = owner;
        m_ctx->sp_cache[el].owner_nvals = nv;
        m_ctx->sp_cache[el].Sp = *out;
        *keep = true;
    }

done:
    return info;
}

static GrB_Info pat_S_cayley_fast(GrB_Matrix *out, GrB_Matrix S,
                                 const Pat_Context *ctx) {
    GrB_Info info = GrB_SUCCESS;
    GrB_Matrix K = NULL;
    GrB_Index N = ctx->N, np = ctx->np;
    *out = NULL;

    // 1. K = I_N (x) S of size (N * np) x (N * N * np)
    PAT_TRY(GrB_Matrix_new(&K, GrB_BOOL, N * np, N * N * np));
    PAT_TRY(GrB_kronecker(K, GrB_NULL, GrB_NULL, GxB_ANY_PAIR_BOOL, ctx->I_N, S,
                         GrB_NULL));

    // 2. out = K * Pbig of size (N * np) x (N * np)
    PAT_TRY(pat_mxm(out, K, ctx->Pbig));

done:
    GrB_free(&K);
    return info;
}

static GrB_Info pat_repeat_diag(GrB_Matrix *out, GrB_Matrix in, GrB_Index times,
                               const Pat_Context *ctx) {
    GrB_Info info = GrB_SUCCESS;
    GrB_Index nrows, ncols;
    *out = NULL;
    PAT_TRY(GrB_Matrix_nrows(&nrows, in));
    PAT_TRY(GrB_Matrix_ncols(&ncols, in));
    if (nrows != ncols) {
        PAT_FAIL(GrB_DIMENSION_MISMATCH, "repeat_diag requires a square matrix");
    }
    if (ctx == NULL || ctx->I_N == NULL) {
        PAT_FAIL(GrB_INVALID_VALUE, "pat_repeat_diag requires ctx->I_N");
    }

    PAT_TRY(GrB_Matrix_new(out, GrB_BOOL, nrows * times, ncols * times));
    PAT_TRY(GrB_kronecker(*out, GrB_NULL, GrB_NULL, GxB_ANY_PAIR_BOOL, ctx->I_N, in,
                         GrB_NULL));
done:
    return info;
}

static GrB_Info pat_lift_fast(GrB_Matrix *out, GrB_Matrix in, const Pat_Context *ctx,
                            GrB_Index n, uint32_t R, const LAGraph_Pat_state_map *T,
                            lift_mode mode) {
    GrB_Info info = GrB_SUCCESS;
    *out = NULL;

    if (mode == LIFT_DIAG) {
        GrB_Matrix base_diag = NULL;
        PAT_TRY(pat_lift(&base_diag, in, n, R, T, LIFT_DIAG));

        if (ctx != NULL && ctx->I_N != NULL && ctx->N > 1) {
            GrB_Matrix tiled = NULL;
            PAT_TRY(pat_repeat_diag(&tiled, base_diag, ctx->N, ctx));
            GrB_free(&base_diag);
            *out = tiled;
        } else {
            *out = base_diag;
        }
        return GrB_SUCCESS;
    }

    if (mode == LIFT_SUM) {
        GrB_Matrix T_local = NULL;
        bool free_T = false;

        if (T != NULL) {
            PAT_TRY(pat_make_T_matrix(&T_local, T, R));
            free_T = true;
        } else if (ctx != NULL && ctx->I_R != NULL) {
            T_local = ctx->I_R;
        } else {
            PAT_TRY(pat_make_T_matrix(&T_local, NULL, R));
            free_T = true;
        }

        GrB_Matrix X = NULL;
        PAT_TRY(pat_fold_stack(&X, in, n, ctx));

        GrB_Index rT, cT, rX, cX;
        PAT_TRY(GrB_Matrix_nrows(&rT, T_local));
        PAT_TRY(GrB_Matrix_ncols(&cT, T_local));
        PAT_TRY(GrB_Matrix_nrows(&rX, X));
        PAT_TRY(GrB_Matrix_ncols(&cX, X));

        GrB_Index out_rows = rT * rX;
        GrB_Index out_cols = cT * cX;

        GrB_Index expected_np = n * R;
        if (out_rows != expected_np || out_cols != expected_np) {
            GrB_free(&X);
            if (free_T) {
                GrB_free(&T_local);
            }
            PAT_FAIL(GrB_DIMENSION_MISMATCH,
                    "LIFT_SUM dimension mismatch: got %lux%lu, expected %lux%lu",
                    (unsigned long)out_rows, (unsigned long)out_cols,
                    (unsigned long)expected_np, (unsigned long)expected_np);
        }

        PAT_TRY(GrB_Matrix_new(out, GrB_BOOL, out_rows, out_cols));
        PAT_TRY(GrB_kronecker(*out, GrB_NULL, GrB_NULL, GxB_ANY_PAIR_BOOL, T_local, X,
                             GrB_NULL));

done:
        GrB_free(&X);
        if (free_T) {
            GrB_free(&T_local);
        }
        if (info < GrB_SUCCESS && *out != NULL) {
            GrB_free(out);
        }
        return info;
    }

    return pat_lift(out, in, n, R, T, mode);
}

static GrB_Info pat_S_perm(GrB_Matrix *out, GrB_Matrix S, GrB_Index np, GrB_Index N,
                          LAGraph_Pat_group g, GrB_Index el) {
    GrB_Info info = GrB_SUCCESS;
    pat_tup t = {0};
    *out = NULL;
    PAT_TRY(tup_from_matrix(&t, S));
    for (GrB_Index i = 0; i < t.n; i++) {
        GrB_Index j = t.c[i] / np, cc = t.c[i] % np;
        t.c[i] = pat_inv(g, N, j, el) * np + cc;
    }
    PAT_TRY(tup_to_matrix(out, &t, np, N * np));
done:
    tup_free(&t);
    return info;
}

static GrB_Info pat_grid_to_stack(GrB_Matrix *out, GrB_Matrix P, GrB_Index np,
                                 GrB_Index rb, GrB_Index cb) {
    GrB_Info info = GrB_SUCCESS;
    pat_tup t = {0};
    *out = NULL;
    PAT_TRY(tup_from_matrix(&t, P));
    for (GrB_Index i = 0; i < t.n; i++) {
        GrB_Index I = t.r[i] / np, rr = t.r[i] % np;
        GrB_Index J = t.c[i] / np, cc = t.c[i] % np;
        t.r[i] = (I * cb + J) * np + rr;
        t.c[i] = cc;
    }
    PAT_TRY(tup_to_matrix(out, &t, rb * cb * np, np));
done:
    tup_free(&t);
    return info;
}

static GrB_Info pat_grid_fold_groups(GrB_Matrix *out, GrB_Matrix E, GrB_Index np,
                                    GrB_Index group, GrB_Index groups) {
    GrB_Info info = GrB_SUCCESS;
    pat_tup t = {0};
    *out = NULL;
    PAT_TRY(tup_from_matrix(&t, E));
    for (GrB_Index i = 0; i < t.n; i++) {
        GrB_Index blk = t.r[i] / np;
        GrB_Index rr = t.r[i] % np;
        GrB_Index g = blk / group;
        t.r[i] = rr;
        t.c[i] = g * np + t.c[i];
    }
    PAT_TRY(tup_to_matrix(out, &t, np, groups * np));
done:
    tup_free(&t);
    return info;
}

//------------------------------------------------------------------------------
// Operands and Caches
//------------------------------------------------------------------------------

typedef struct {
    GrB_Matrix M;
    Matrix *hold; // Merged copy of a lazy matrix (owned), NULL otherwise
} pat_operand;

static GrB_Info pat_operand_get(Matrix *m, int8_t opt, pat_operand *op) {
    GrB_Info info = GrB_SUCCESS;
    op->hold = NULL;
    if (!m->is_lazy) {
        op->M = m->base;
        return GrB_SUCCESS;
    }
    PAT_TRY(CFL_matrix_to_base(&op->hold, m, opt));
    op->M = op->hold->base;
done:
    return info;
}

static void pat_operand_free(pat_operand *op) {
    if (op->hold != NULL) {
        CFL_matrix_free(&op->hold);
    }
    op->M = NULL;
}

static GrB_Matrix cache_get(const Pat_Context *ctx, const void *key,
                            const Matrix *owner, GrB_Index nv) {
    if (!ctx || !key || !owner) {
        return NULL;
    }
    for (size_t i = 0; i < ctx->rule_cache_count; i++) {
        const pat_rule_cache_slot *s = &ctx->rule_cache[i];
        if (s->key == key && s->owner == owner && s->owner_nvals == nv) {
            return s->matrix;
        }
    }
    return NULL;
}

static bool cache_put(const Pat_Context *ctx, const void *key,
                      const Matrix *owner, GrB_Index nv, GrB_Matrix M) {
    if (!ctx || !key || !owner) {
        return false;
    }
    Pat_Context *c = (Pat_Context *)ctx;

    for (size_t i = 0; i < c->rule_cache_count; i++) {
        pat_rule_cache_slot *s = &c->rule_cache[i];
        if (s->key == key && s->owner == owner) {
            if (s->matrix != NULL && s->matrix != M) {
                GrB_free(&s->matrix);
            }
            s->owner_nvals = nv;
            s->matrix = M;
            return true;
        }
    }

    if (c->rule_cache_count >= c->rule_cache_cap) {
        size_t cap = c->rule_cache_cap ? 2 * c->rule_cache_cap : 16;
        pat_rule_cache_slot *p = realloc(c->rule_cache, cap * sizeof(*p));
        if (!p) {
            return false;
        }
        c->rule_cache = p;
        c->rule_cache_cap = cap;
    }
    c->rule_cache[c->rule_cache_count++] = (pat_rule_cache_slot){key, owner, nv, M};
    return true;
}

static GrB_Info get_lift(GrB_Matrix *L, bool *keep, Matrix *owner, const void *key,
                         GrB_Matrix X, GrB_Index n, uint32_t R,
                         const LAGraph_Pat_state_map *T, lift_mode mode,
                         const Pat_Context *ctx) {
    GrB_Info info = GrB_SUCCESS;
    *keep = false;
    GrB_Index nv = 0;
    bool cacheable = owner_nvals_of(owner, &nv);

    if (cacheable && (*L = cache_get(ctx, key, owner, nv)) != NULL) {
        *keep = true;
        return GrB_SUCCESS;
    }

    PAT_TRY(pat_lift_fast(L, X, ctx, n, R, T, mode));

    if (cacheable) {
        if (cache_put(ctx, key, owner, nv, *L)) {
            *keep = true;
        } else {
            *keep = false;
        }
    } else {
        *keep = false;
    }

done:
    return info;
}

//------------------------------------------------------------------------------
// Kernels. A, B are operands in grammar order (prod_A, prod_B)
//------------------------------------------------------------------------------

typedef struct {
    const LAGraph_rule_Pat *pat;
    GrB_Matrix A, B;
    Matrix *ownerA, *ownerB;
    GrB_Index n, np, N;
    uint32_t R, k;
    const Pat_Context *ctx;
} pat_args;

static GrB_Info stack_count(GrB_Matrix X, GrB_Index n, GrB_Index *count) {
    GrB_Info info = GrB_SUCCESS;
    GrB_Index nr, nc;
    PAT_TRY(GrB_Matrix_nrows(&nr, X));
    PAT_TRY(GrB_Matrix_ncols(&nc, X));
    *count = (nr > nc ? nr : nc) / n;
done:
    return info;
}

static GrB_Info k_scale(GrB_Matrix *res, const pat_args *a) {
    GrB_Info info = GrB_SUCCESS;
    GrB_Matrix L = NULL;
    bool keep = false;

    PAT_TRY(get_lift(&L, &keep, a->ownerA, a->pat, a->A, a->n, a->R, NULL, LIFT_SUM,
                    a->ctx));
    PAT_TRY(pat_mxm(res, L, a->B));

done:
    if (!keep) {
        GrB_free(&L);
    }
    return info;
}

static GrB_Info k_right(GrB_Matrix *res, const pat_args *a) {
    GrB_Info info = GrB_SUCCESS;
    GrB_Matrix Bl = NULL, Sv = NULL, P = NULL;
    bool keep = false;
    GrB_Index cnt;
    PAT_TRY(stack_count(a->B, a->n, &cnt));
    if (cnt != a->k) {
        PAT_FAIL(GrB_DIMENSION_MISMATCH, "RIGHT: B has %lu blocks, descriptor says %u",
                (unsigned long)cnt, a->k);
    }
    PAT_TRY(get_lift(&Bl, &keep, a->ownerB, a->pat, a->B, a->n, a->R, NULL, LIFT_HORIZ,
                    a->ctx));
    PAT_TRY(pat_S_vert(&Sv, a->A, a->np, a->N));
    PAT_TRY(pat_mxm(&P, Sv, Bl));
    PAT_TRY(pat_grid_to_stack(res, P, a->np, a->N, a->k));

done:
    if (!keep) {
        GrB_free(&Bl);
    }
    GrB_free(&Sv);
    GrB_free(&P);
    return info;
}

static GrB_Info k_left(GrB_Matrix *res, const pat_args *a) {
    GrB_Info info = GrB_SUCCESS;
    GrB_Matrix Ad = NULL;
    bool keep = false;
    GrB_Index cnt;
    PAT_TRY(stack_count(a->A, a->n, &cnt));
    if (cnt != a->k) {
        PAT_FAIL(GrB_DIMENSION_MISMATCH, "LEFT: A has %lu blocks, descriptor says %u",
                (unsigned long)cnt, a->k);
    }
    PAT_TRY(get_lift(&Ad, &keep, a->ownerA, a->pat, a->A, a->n, a->R, NULL, LIFT_DIAG,
                    a->ctx));
    PAT_TRY(pat_mxm(res, Ad, a->B));
done:
    if (!keep) {
        GrB_free(&Ad);
    }
    return info;
}

static GrB_Info k_conv_all(GrB_Matrix *res, const pat_args *a) {
    GrB_Info info = GrB_SUCCESS;
    GrB_Matrix Eb = NULL, Cay = NULL;
    bool keep = false;

    PAT_TRY(pat_grid_fold_groups(&Eb, a->A, a->np, a->k, a->N));

    GrB_Index current_b_nvals = 0;
    PAT_TRY(GrB_Matrix_nvals(&current_b_nvals, a->B));

    GrB_Index ownerB_nv = 0;
    bool cacheable = owner_nvals_of(a->ownerB, &ownerB_nv);

    pat_rule_cache_slot *slot = NULL;
    if (a->ctx != NULL && a->pat != NULL) {
        Pat_Context *c = (Pat_Context *)a->ctx;
        for (size_t i = 0; i < c->rule_cache_count; i++) {
            if (c->rule_cache[i].key == a->pat) {
                slot = &c->rule_cache[i];
                break;
            }
        }
        if (slot == NULL) {
            if (c->rule_cache_count >= c->rule_cache_cap) {
                size_t cap = c->rule_cache_cap ? 2 * c->rule_cache_cap : 16;
                pat_rule_cache_slot *p = realloc(c->rule_cache, cap * sizeof(*p));
                if (p != NULL) {
                    c->rule_cache = p;
                    c->rule_cache_cap = cap;
                }
            }
            if (c->rule_cache_count < c->rule_cache_cap) {
                slot = &c->rule_cache[c->rule_cache_count++];
                slot->key = a->pat;
                slot->owner = a->ownerB;
                slot->owner_nvals = 0;
                slot->matrix = NULL;
                slot->cay_delta = NULL;
                slot->delta_nvals = 0;
            }
        }
    }

    if (!cacheable) {
        if (a->ctx != NULL) {
            PAT_TRY(pat_S_cayley_fast(&Cay, a->B, a->ctx));
        } else {
            PAT_TRY(pat_S_cayley(&Cay, a->B, a->np, a->N, a->pat->group));
        }

        if (slot != NULL) {
            if (slot->cay_delta != NULL) {
                GrB_free(&slot->cay_delta);
            }
            slot->cay_delta = Cay;
            slot->delta_nvals = current_b_nvals;
            keep = true;
        }
    } else {
        bool incremental_success = false;

        if (slot != NULL && slot->matrix != NULL && slot->cay_delta != NULL) {
            GrB_Index old_nv = slot->owner_nvals;
            GrB_Index d_nv = slot->delta_nvals;

            if (old_nv + d_nv == ownerB_nv) {
                if (d_nv == 0) {
                    Cay = slot->matrix;
                    keep = true;
                    incremental_success = true;
                } else {
                    GrB_Matrix Cay_new = NULL;
                    GrB_Index nr, nc;
                    PAT_TRY(GrB_Matrix_nrows(&nr, slot->matrix));
                    PAT_TRY(GrB_Matrix_ncols(&nc, slot->matrix));
                    PAT_TRY(GrB_Matrix_new(&Cay_new, GrB_BOOL, nr, nc));
                    PAT_TRY(GrB_eWiseAdd(Cay_new, GrB_NULL, GrB_NULL, GrB_LOR,
                                        slot->matrix, slot->cay_delta, GrB_NULL));

                    GrB_free(&slot->matrix);
                    slot->matrix = Cay_new;
                    slot->owner_nvals = ownerB_nv;

                    GrB_free(&slot->cay_delta);
                    slot->cay_delta = NULL;
                    slot->delta_nvals = 0;

                    Cay = slot->matrix;
                    keep = true;
                    incremental_success = true;
                }
            }
        }

        if (!incremental_success) {
            if (a->ctx != NULL) {
                PAT_TRY(pat_S_cayley_fast(&Cay, a->B, a->ctx));
            } else {
                PAT_TRY(pat_S_cayley(&Cay, a->B, a->np, a->N, a->pat->group));
            }

            if (slot != NULL) {
                if (slot->matrix != NULL && slot->matrix != Cay) {
                    GrB_free(&slot->matrix);
                }
                slot->matrix = Cay;
                slot->owner_nvals = ownerB_nv;
                if (slot->cay_delta != NULL) {
                    GrB_free(&slot->cay_delta);
                    slot->cay_delta = NULL;
                }
                keep = true;
            }
        }
    }

    PAT_TRY(pat_mxm(res, Eb, Cay));

done:
    GrB_free(&Eb);
    if (!keep) {
        GrB_free(&Cay);
    }
    return info;
}

static GrB_Info k_conv_el(GrB_Matrix *res, const pat_args *a) {
    GrB_Info info = GrB_SUCCESS;
    GrB_Matrix L = NULL, Sp = NULL;
    bool keep_L = false, keep_Sp = false;

    PAT_TRY(get_lift(&L, &keep_L, a->ownerA, a->pat, a->A, a->n, a->R, a->pat->state,
                    LIFT_SUM, a->ctx));

    if (a->ctx != NULL) {
        PAT_TRY(pat_S_perm_fast(&Sp, a->B, a->ctx, (GrB_Index)a->pat->element, a->ownerB,
                               &keep_Sp));
    } else {
        PAT_TRY(pat_S_perm(&Sp, a->B, a->np, a->N, a->pat->group,
                          (GrB_Index)a->pat->element));
        keep_Sp = false;
    }

    PAT_TRY(pat_mxm(res, L, Sp));
done:
    if (!keep_L) {
        GrB_free(&L);
    }
    if (!keep_Sp) {
        GrB_free(&Sp);
    }
    return info;
}

static GrB_Info k_project(GrB_Matrix *res, const pat_args *a, GrB_Index n_plain) {
    GrB_Info info = GrB_SUCCESS;
    GrB_Matrix blk = NULL;
    GrB_Index np = n_plain * a->R;
    int64_t off = (int64_t)a->pat->block_symbol - a->pat->role[1].base;
    int64_t pattern_span = (int64_t)a->pat->masks * a->pat->states * a->pat->states;
    if (off < 0 || off >= pattern_span) {
        PAT_FAIL(GrB_INDEX_OUT_OF_BOUNDS,
                "PROJECT: block symbol %d is outside S pattern", a->pat->block_symbol);
    }
    GrB_Index m = (GrB_Index)(off / ((int64_t)a->pat->states * a->pat->states));
    GrB_Index qoff = (GrB_Index)(off % ((int64_t)a->pat->states * a->pat->states));
    GrB_Index qr = qoff / a->pat->states;
    GrB_Index qc = qoff % a->pat->states;
    GrB_Index I[2] = {qr * n_plain, qr * n_plain + n_plain - 1};
    GrB_Index J[2] = {m * np + qc * n_plain, m * np + qc * n_plain + n_plain - 1};
    PAT_TRY(GrB_Matrix_new(&blk, GrB_BOOL, n_plain, n_plain));
    PAT_TRY(GrB_Matrix_extract(blk, GrB_NULL, GrB_NULL, a->A, I, GxB_RANGE, J, GxB_RANGE,
                              GrB_NULL));
    PAT_TRY(pat_mxm(res, blk, a->B));
done:
    GrB_free(&blk);
    return info;
}

//------------------------------------------------------------------------------
// Entry point called from matrix_mxm_block
//------------------------------------------------------------------------------

GrB_Info CFL_Pat_matrix_mxm(Matrix *output, Matrix *first, Matrix *second, bool accum,
                       bool swap, int8_t optimizations, const LAGraph_rule_Pat *pat,
                       const Pat_Context *ctx) {
    GrB_Info info = GrB_SUCCESS;
    pat_operand of = {0}, os = {0};
    GrB_Matrix res = NULL;
    Matrix *tmp = NULL;
    bool have_ops = false;

    if (pat == NULL || !(optimizations & OPT_BLOCK) || !(optimizations & OPT_PAT)) {
        return GrB_INVALID_VALUE;
    }

    if (!accum) {
        PAT_TRY(CFL_clear(output, optimizations));
    }

    PAT_TRY(CFL_matrix_update(first));
    PAT_TRY(CFL_matrix_update(second));
    if (first->nvals == 0 || second->nvals == 0) {
        return GrB_SUCCESS;
    }

    PAT_TRY(pat_operand_get(first, optimizations, &of));
    PAT_TRY(pat_operand_get(second, optimizations, &os));
    have_ops = true;

    pat_args a;
    memset(&a, 0, sizeof a);
    a.pat = pat;
    a.ctx = ctx;
    a.A = swap ? os.M : of.M;
    a.B = swap ? of.M : os.M;
    a.ownerA = swap ? NULL : first;
    a.ownerB = swap ? first : NULL;
    a.N = pat->masks;
    a.R = pat->states;
    a.k = pat->idx_count;

    Matrix *Aop = swap ? second : first;
    Matrix *Bop = swap ? first : second;
    switch (pat->kind) {
        case LAGraph_PAT_SCALE:
        case LAGraph_PAT_CONV:
            a.np = Bop->nrows; // prod_B is S
            break;
        case LAGraph_PAT_RIGHT:
        case LAGraph_PAT_PROJECT:
            a.np = Aop->nrows; // prod_A is S
            break;
        case LAGraph_PAT_LEFT:
            a.np = Bop->ncols; // prod_B is (N*k*np) x np
            break;
        default:
            PAT_FAIL(GrB_INVALID_VALUE, "kind %d is not a binary rule", (int)pat->kind);
    }
    if (a.R == 0 || a.N == 0 || a.np % a.R != 0) {
        PAT_FAIL(GrB_DIMENSION_MISMATCH, "bad descriptor/operand sizes (np=%lu, R=%u)",
                (unsigned long)a.np, a.R);
    }
    a.n = a.np / a.R;

    switch (pat->kind) {
        case LAGraph_PAT_SCALE:
            PAT_TRY(k_scale(&res, &a));
            break;
        case LAGraph_PAT_RIGHT:
            PAT_TRY(k_right(&res, &a));
            break;
        case LAGraph_PAT_LEFT:
            PAT_TRY(k_left(&res, &a));
            break;
        case LAGraph_PAT_CONV:
            if (pat->element == LAGraph_PAT_ALL_ELEMENTS) {
                PAT_TRY(k_conv_all(&res, &a));
            } else {
                PAT_TRY(k_conv_el(&res, &a));
            }
            break;
        case LAGraph_PAT_PROJECT: {
            GrB_Index ncB;
            PAT_TRY(GrB_Matrix_ncols(&ncB, a.B));
            PAT_TRY(k_project(&res, &a, ncB));
            break;
        }
        default:
            PAT_FAIL(GrB_INVALID_VALUE, "unsupported kind");
    }

    GrB_Index nv = 0;
    PAT_TRY(GrB_Matrix_nvals(&nv, res));
    if (nv > 0) {
        PAT_TRY(CFL_matrix_from_base(&tmp, res));
        res = NULL; // Owned by tmp
        PAT_TRY(matrix_wise_block(output, output, tmp, false, optimizations));
    }

done:
    GrB_free(&res);
    if (tmp != NULL) {
        CFL_matrix_free(&tmp);
    }
    if (have_ops) {
        pat_operand_free(&of);
        pat_operand_free(&os);
    }
    return info;
}

//------------------------------------------------------------------------------
// Epsilon rules and output
//------------------------------------------------------------------------------

GrB_Info CFL_Pat_eps(Matrix *delta_S, const LAGraph_rule_Pat *pat, GrB_Index n,
                    int8_t optimizations) {
    GrB_Info info = GrB_SUCCESS;
    pat_tup t = {0};
    GrB_Matrix M = NULL;
    Matrix *tmp = NULL;
    GrB_Index np = n * pat->states;
    int64_t off = (int64_t)pat->block_symbol - pat->role[0].base;
    int64_t span = (int64_t)pat->masks * pat->states * pat->states;
    if (off < 0 || off >= span) {
        PAT_FAIL(GrB_INDEX_OUT_OF_BOUNDS, "EPS: block symbol %d is outside S pattern",
                pat->block_symbol);
    }
    GrB_Index m = (GrB_Index)(off / ((int64_t)pat->states * pat->states));
    GrB_Index qoff = (GrB_Index)(off % ((int64_t)pat->states * pat->states));
    GrB_Index qr = qoff / pat->states;
    GrB_Index qc = qoff % pat->states;

    PAT_TRY(tup_alloc(&t, n));
    for (GrB_Index x = 0; x < n; x++) {
        t.r[x] = qr * n + x;
        t.c[x] = m * np + qc * n + x;
    }
    t.n = n;
    PAT_TRY(tup_to_matrix(&M, &t, np, (GrB_Index)pat->masks * np));
    PAT_TRY(CFL_matrix_from_base(&tmp, M));
    M = NULL;
    PAT_TRY(CFL_wise(delta_S, delta_S, tmp, true, optimizations));

done:
    tup_free(&t);
    GrB_free(&M);
    if (tmp != NULL) {
        CFL_matrix_free(&tmp);
    }
    return info;
}

GrB_Info CFL_Pat_shape(const LAGraph_Pat_pattern *pat, GrB_Index n, GrB_Index *nrows,
                          GrB_Index *ncols) {
    GrB_Index np = n * pat->states;
    switch (pat->role.kind) {
        case LAGraph_PAT_SYM_S:
            *nrows = np;
            *ncols = (GrB_Index)pat->masks * np;
            break;
        case LAGraph_PAT_SYM_PATILY:
            *nrows = (GrB_Index)pat->masks * pat->idx_count * np;
            *ncols = np;
            break;
        default:
            return GrB_INVALID_VALUE;
    }
    return GrB_SUCCESS;
}

static int64_t pattern_span(const LAGraph_Pat_pattern *f) {
    int64_t s = (int64_t)f->masks * f->states * f->states;
    return f->role.kind == LAGraph_PAT_SYM_PATILY ? s * f->idx_count : s;
}

GrB_Info CFL_Pat_split(GrB_Matrix *outputs, Matrix *matrix,
                      const LAGraph_Pat_pattern *pat, GrB_Index n,
                      int8_t optimizations) {
    GrB_Info info = GrB_SUCCESS;
    pat_operand op = {0};
    pat_tup t = {0};
    GrB_Index *off = NULL, *cnt = NULL, *xs = NULL, *ys = NULL, *pos = NULL;
    int64_t total = pattern_span(pat);
    GrB_Index np = n * pat->states, R = pat->states;
    bool is_pat = pat->role.kind == LAGraph_PAT_SYM_PATILY;

    PAT_TRY(CFL_matrix_update(matrix));
    PAT_TRY(pat_operand_get(matrix, optimizations, &op));
    GrB_Index mr, mc;
    PAT_TRY(GrB_Matrix_nrows(&mr, op.M));
    PAT_TRY(GrB_Matrix_ncols(&mc, op.M));

    GrB_Index expected_rows = is_pat ? (GrB_Index)pat->masks * pat->idx_count * np : np;
    GrB_Index expected_cols = is_pat ? np : (GrB_Index)pat->masks * np;

    if (mr != expected_rows || mc != expected_cols) {
        PAT_FAIL(GrB_DIMENSION_MISMATCH,
                "split: matrix is %lux%lu, expected %lux%lu",
                (unsigned long)mr, (unsigned long)mc,
                (unsigned long)expected_rows, (unsigned long)expected_cols);
    }
    PAT_TRY(tup_from_matrix(&t, op.M));

    if (LAGraph_Calloc((void **)&off, t.n, sizeof(GrB_Index), NULL) < 0 ||
        LAGraph_Calloc((void **)&xs, t.n, sizeof(GrB_Index), NULL) < 0 ||
        LAGraph_Calloc((void **)&ys, t.n, sizeof(GrB_Index), NULL) < 0 ||
        LAGraph_Calloc((void **)&cnt, (size_t)total + 1, sizeof(GrB_Index), NULL) < 0 ||
        LAGraph_Calloc((void **)&pos, (size_t)total + 1, sizeof(GrB_Index), NULL) < 0) {
        PAT_FAIL(GrB_OUT_OF_MEMORY, "split: out of memory");
    }

    for (GrB_Index i = 0; i < t.n; i++) {
        GrB_Index r = t.r[i], c = t.c[i];
        GrB_Index blk = r / np, rr = r % np;
        GrB_Index m, idx, cc;
        if (is_pat) {
            m   = blk / pat->idx_count;
            idx = blk % pat->idx_count;
            cc  = c;
        } else {
            m   = c / np;
            idx = 0;
            cc  = c % np;
        }
        GrB_Index qr = rr / n, qc = cc / n;
        int64_t o = (int64_t)m * pat->role.mask_stride + (int64_t)qr * pat->role.qrow_stride +
                    (int64_t)qc * pat->role.qcol_stride + (int64_t)idx;
        if (o < 0 || o >= total) {
            PAT_FAIL(GrB_INDEX_OUT_OF_BOUNDS, "split: id offset %ld outside [0,%ld)",
                    (long)o, (long)total);
        }
        off[i] = (GrB_Index)o;
        xs[i] = rr % n;
        ys[i] = cc % n;
        cnt[o + 1]++;
    }

    for (int64_t o = 0; o < total; o++) {
        cnt[o + 1] += cnt[o];
    }
    memcpy(pos, cnt, ((size_t)total + 1) * sizeof(GrB_Index));

    GrB_Index *sx = NULL, *sy = NULL;
    if (LAGraph_Calloc((void **)&sx, t.n, sizeof(GrB_Index), NULL) < 0 ||
        LAGraph_Calloc((void **)&sy, t.n, sizeof(GrB_Index), NULL) < 0) {
        LAGraph_Free((void **)&sx, NULL);
        LAGraph_Free((void **)&sy, NULL);
        PAT_FAIL(GrB_OUT_OF_MEMORY, "split: out of memory");
    }
    for (GrB_Index i = 0; i < t.n; i++) {
        GrB_Index p = pos[off[i]]++;
        sx[p] = xs[i];
        sy[p] = ys[i];
    }
    for (int64_t o = 0; o < total && info >= GrB_SUCCESS; o++) {
        PAT_TRY(build_matrix(&outputs[pat->role.base + o], sx + cnt[o], sy + cnt[o],
                            cnt[o + 1] - cnt[o], n, n));
    }
    LAGraph_Free((void **)&sx, NULL);
    LAGraph_Free((void **)&sy, NULL);
    (void)R;

done:
    tup_free(&t);
    LAGraph_Free((void **)&off, NULL);
    LAGraph_Free((void **)&xs, NULL);
    LAGraph_Free((void **)&ys, NULL);
    LAGraph_Free((void **)&cnt, NULL);
    LAGraph_Free((void **)&pos, NULL);
    pat_operand_free(&op);
    return info;
}

//------------------------------------------------------------------------------
// Descriptor checks
//------------------------------------------------------------------------------

int64_t CFL_Pat_span(const LAGraph_rule_Pat *pat, int role_index) {
    const LAGraph_Pat_role *r = &pat->role[role_index];
    int64_t s = (int64_t)pat->masks * pat->states * pat->states;
    switch (r->kind) {
        case LAGraph_PAT_SYM_S:
            return s;
        case LAGraph_PAT_SYM_PATILY:
            return s * pat->idx_count;
        default:
            return 0;
    }
}

static const char *pat_expected(LAGraph_Pat_kind kind, bool all,
                               LAGraph_Pat_sym exp[3]) {
    const LAGraph_Pat_sym P = LAGraph_PAT_SYM_PLAIN, S = LAGraph_PAT_SYM_S,
                         F = LAGraph_PAT_SYM_PATILY;
    switch (kind) {
        case LAGraph_PAT_SCALE:
            exp[0] = S, exp[1] = P, exp[2] = S;
            return "SCALE";
        case LAGraph_PAT_RIGHT:
            exp[0] = F, exp[1] = S, exp[2] = P;
            return "RIGHT";
        case LAGraph_PAT_LEFT:
            exp[0] = F, exp[1] = P, exp[2] = F;
            return "LEFT";
        case LAGraph_PAT_CONV:
            exp[0] = S, exp[1] = all ? F : P, exp[2] = S;
            return "CONV";
        case LAGraph_PAT_EPS:
            exp[0] = S, exp[1] = P, exp[2] = P;
            return "EPS";
        case LAGraph_PAT_PROJECT:
            exp[0] = P, exp[1] = S, exp[2] = P;
            return "PROJECT";
        default:
            return NULL;
    }
}

GrB_Info CFL_Pat_check(const LAGraph_rule_Pat *pat, size_t symbols_amount, char *msg) {
    LAGraph_Pat_sym exp[3];
    const char *name =
        pat_expected(pat->kind, pat->element == LAGraph_PAT_ALL_ELEMENTS, exp);
#define Pat_BAD(...)                                                                     \
    do {                                                                                 \
        if (msg) {                                                                       \
            snprintf(msg, LAGRAPH_MSG_LEN, __VA_ARGS__);                                 \
        }                                                                                \
        return GrB_INVALID_VALUE;                                                        \
    } while (0)
    if (name == NULL) {
        Pat_BAD("Pat descriptor has unknown kind %d", (int)pat->kind);
    }
    if (pat->masks == 0 || pat->states == 0 || pat->idx_count == 0) {
        Pat_BAD("Pat %s: masks, states and idx_count must be positive", name);
    }
    for (int j = 0; j < 3; j++) {
        if (pat->role[j].kind != exp[j]) {
            Pat_BAD("Pat %s: role %d has kind %d, expected %d", name, j,
                   (int)pat->role[j].kind, (int)exp[j]);
        }
        if (exp[j] != LAGraph_PAT_SYM_PLAIN) {
            int64_t span = CFL_Pat_span(pat, j);
            if (pat->role[j].base < 0 || (size_t)(pat->role[j].base + span) > symbols_amount) {
                Pat_BAD("Pat %s: role %d ids [%d, %d) are outside [0, %zu)", name, j,
                       pat->role[j].base, (int)(pat->role[j].base + span), symbols_amount);
            }
        }
    }
    if (pat->kind == LAGraph_PAT_CONV && pat->element != LAGraph_PAT_ALL_ELEMENTS &&
        (pat->element < 0 || pat->element >= (int64_t)pat->masks)) {
        Pat_BAD("Pat CONV: element %ld is outside [0, %u)", (long)pat->element, pat->masks);
    }
    if (pat->state != NULL) {
        for (uint32_t e = 0; e < pat->state->nnz; e++) {
            if (pat->state->entries[e].row < 0 ||
                (uint32_t)pat->state->entries[e].row >= pat->states ||
                pat->state->entries[e].col < 0 ||
                (uint32_t)pat->state->entries[e].col >= pat->states) {
                Pat_BAD("Pat %s: state map entry %u is outside [0, %u)", name, e,
                       pat->states);
            }
        }
    }
    if (pat->kind == LAGraph_PAT_EPS) {
        int64_t off = (int64_t)pat->block_symbol - pat->role[0].base;
        int64_t span = (int64_t)pat->masks * pat->states * pat->states;
        if (off < 0 || off >= span) {
            Pat_BAD("Pat EPS: block symbol %d is outside the S pattern",
                   pat->block_symbol);
        }
    }
    if (pat->kind == LAGraph_PAT_PROJECT) {
        int64_t off = (int64_t)pat->block_symbol - pat->role[1].base;
        int64_t span = (int64_t)pat->masks * pat->states * pat->states;
        if (off < 0 || off >= span) {
            Pat_BAD("Pat PROJECT: block symbol %d is outside the S pattern",
                   pat->block_symbol);
        }
    }
#undef Pat_BAD
    return GrB_SUCCESS;
}

static GrB_Info pat_make_Pel(GrB_Matrix *P, GrB_Index np, GrB_Index N,
                            LAGraph_Pat_group g, GrB_Index el) {
    GrB_Info info = GrB_SUCCESS;
    GrB_Index nz = N * np;
    GrB_Index *r = NULL, *c = NULL;
    if (LAGraph_Malloc((void **)&r, nz, sizeof(GrB_Index), NULL) < 0 ||
        LAGraph_Malloc((void **)&c, nz, sizeof(GrB_Index), NULL) < 0) {
        LAGraph_Free((void **)&r, NULL);
        LAGraph_Free((void **)&c, NULL);
        return GrB_OUT_OF_MEMORY;
    }

    GrB_Index d = 0;
    for (GrB_Index j = 0; j < N; j++) {
        GrB_Index m = pat_inv(g, N, j, el);
        for (GrB_Index x = 0; x < np; x++) {
            r[d] = j * np + x;
            c[d] = m * np + x;
            d++;
        }
    }

    PAT_TRY(build_matrix(P, r, c, nz, N * np, N * np));
done:
    LAGraph_Free((void **)&r, NULL);
    LAGraph_Free((void **)&c, NULL);
    return info;
}

static GrB_Info pat_make_T_matrix(GrB_Matrix *T_out, const LAGraph_Pat_state_map *T,
                                 uint32_t R) {
    GrB_Info info = GrB_SUCCESS;
    uint32_t nT = T ? T->nnz : R;
    GrB_Index *r = NULL, *c = NULL;
    if (LAGraph_Malloc((void **)&r, nT, sizeof(GrB_Index), NULL) < 0 ||
        LAGraph_Malloc((void **)&c, nT, sizeof(GrB_Index), NULL) < 0) {
        LAGraph_Free((void **)&r, NULL);
        LAGraph_Free((void **)&c, NULL);
        return GrB_OUT_OF_MEMORY;
    }

    if (T) {
        for (uint32_t e = 0; e < nT; e++) {
            r[e] = T->entries[e].row;
            c[e] = T->entries[e].col;
        }
    } else {
        for (uint32_t e = 0; e < R; e++) {
            r[e] = e;
            c[e] = e;
        }
    }

    PAT_TRY(build_matrix(T_out, r, c, nT, R, R));
done:
    LAGraph_Free((void **)&r, NULL);
    LAGraph_Free((void **)&c, NULL);
    return info;
}

//------------------------------------------------------------------------------
// Context Initialization and Destruction
//------------------------------------------------------------------------------

GrB_Info CFL_Pat_context_init(Pat_Context *ctx, GrB_Index N, GrB_Index R, GrB_Index np,
                         LAGraph_Pat_group g) {
    GrB_Info info = GrB_SUCCESS;
    memset(ctx, 0, sizeof(*ctx));
    ctx->N = N;
    ctx->R = R;
    ctx->np = np;
    ctx->group = g;

    if (LAGraph_Malloc((void **)&ctx->P_el, N, sizeof(GrB_Matrix), NULL) < 0) {
        return GrB_OUT_OF_MEMORY;
    }
    for (GrB_Index i = 0; i < N; i++) {
        ctx->P_el[i] = NULL;
    }

    for (GrB_Index el = 0; el < N; el++) {
        PAT_TRY(pat_make_Pel(&ctx->P_el[el], np, N, g, el));
    }

    if (LAGraph_Calloc((void **)&ctx->sp_cache, N, sizeof(pat_sp_cache_slot), NULL) < 0) {
        return GrB_OUT_OF_MEMORY;
    }
    for (GrB_Index i = 0; i < N; i++) {
        ctx->sp_cache[i].owner = NULL;
        ctx->sp_cache[i].owner_nvals = 0;
        ctx->sp_cache[i].Sp = NULL;
    }

    PAT_TRY(pat_make_T_matrix(&ctx->I_R, NULL, (uint32_t)R));

    GrB_Vector v = NULL;
    PAT_TRY(GrB_Vector_new(&v, GrB_BOOL, np));
    PAT_TRY(GrB_Vector_assign_BOOL(v, NULL, NULL, true, GrB_ALL, np, NULL));
    PAT_TRY(GrB_Matrix_diag(&ctx->I_np, v, 0));
    GrB_Vector_free(&v);

    GrB_Vector v_N = NULL;
    PAT_TRY(GrB_Vector_new(&v_N, GrB_BOOL, N));
    PAT_TRY(GrB_Vector_assign_BOOL(v_N, NULL, NULL, true, GrB_ALL, N, NULL));
    PAT_TRY(GrB_Matrix_diag(&ctx->I_N, v_N, 0));
    GrB_Vector_free(&v_N);

    GrB_Index nz_pi = N * N;
    GrB_Index *r_pi = NULL, *c_pi = NULL;
    if (LAGraph_Malloc((void **)&r_pi, nz_pi, sizeof(GrB_Index), NULL) < 0 ||
        LAGraph_Malloc((void **)&c_pi, nz_pi, sizeof(GrB_Index), NULL) < 0) {
        LAGraph_Free((void **)&r_pi, NULL);
        LAGraph_Free((void **)&c_pi, NULL);
        return GrB_OUT_OF_MEMORY;
    }

    GrB_Index d = 0;
    for (GrB_Index el = 0; el < N; el++) {
        for (GrB_Index j = 0; j < N; j++) {
            r_pi[d] = el * N + j;
            c_pi[d] = pat_inv(g, N, j, el);
            d++;
        }
    }

    GrB_Matrix Pi_all = NULL;
    PAT_TRY(build_matrix(&Pi_all, r_pi, c_pi, nz_pi, N * N, N));
    LAGraph_Free((void **)&r_pi, NULL);
    LAGraph_Free((void **)&c_pi, NULL);
    r_pi = NULL;
    c_pi = NULL;

    PAT_TRY(GrB_Matrix_new(&ctx->Pbig, GrB_BOOL, N * N * np, N * np));
    PAT_TRY(GrB_kronecker(ctx->Pbig, GrB_NULL, GrB_NULL, GxB_ANY_PAIR_BOOL, Pi_all,
                       ctx->I_np, GrB_NULL));
    GrB_free(&Pi_all);

done:
    LAGraph_Free((void **)&r_pi, NULL);
    LAGraph_Free((void **)&c_pi, NULL);
    GrB_Vector_free(&v);
    GrB_Vector_free(&v_N);
    GrB_free(&Pi_all);
    if (info < GrB_SUCCESS) {
        CFL_Pat_context_free(ctx);
    }
    return info;
}

void CFL_Pat_context_free(Pat_Context *ctx) {
    if (ctx->P_el) {
        for (GrB_Index el = 0; el < ctx->N; el++) {
            if (ctx->P_el[el]) {
                GrB_free(&ctx->P_el[el]);
            }
        }
        LAGraph_Free((void **)&ctx->P_el, NULL);
    }
    if (ctx->sp_cache) {
        for (GrB_Index i = 0; i < ctx->N; i++) {
            if (ctx->sp_cache[i].Sp) {
                GrB_free(&ctx->sp_cache[i].Sp);
            }
        }
        LAGraph_Free((void **)&ctx->sp_cache, NULL);
    }
    if (ctx->rule_cache) {
        for (size_t i = 0; i < ctx->rule_cache_count; i++) {
            if (ctx->rule_cache[i].matrix) {
                GrB_free(&ctx->rule_cache[i].matrix);
            }
            if (ctx->rule_cache[i].cay_delta) {
                GrB_free(&ctx->rule_cache[i].cay_delta);
            }
        }
        free(ctx->rule_cache);
    }
    if (ctx->I_R) {
        GrB_free(&ctx->I_R);
    }
    if (ctx->I_np) {
        GrB_free(&ctx->I_np);
    }
    if (ctx->I_N) {
        GrB_free(&ctx->I_N);
    }
    if (ctx->Pbig) {
        GrB_free(&ctx->Pbig);
    }

    if (ctx->fold_cache) {
        for (size_t i = 0; i < ctx->fold_cache_count; i++) {
            GrB_free(&ctx->fold_cache[i].F);
        }
        free(ctx->fold_cache);
    }

    memset(ctx, 0, sizeof(*ctx));
}
