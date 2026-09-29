//------------------------------------------------------------------------------
// LAGraph_CFL_reachability.c: Context-Free Language Reachability Matrix-Based
// Algorithm
// ------------------------------------------------------------------------------
//
// LAGraph, (c) 2019-2024 by The LAGraph Contributors, All Rights Reserved.
// SPDX-License-Identifier: BSD-2-Clause

// Contributed by Ilhom Kombaev, Semyon Grigoriev, St. Petersburg State University.

//------------------------------------------------------------------------------

// Code is based on the "A matrix-based CFPQ algorithm" described in the
// following paper: * Rustam Azimov, Semyon Grigorev, "Context-Free Path
// Querying Using Linear Algebra", URL:
// https://disser.spbu.ru/files/2022/disser_azimov.pdf

#define LG_FREE_WORK                                                                     \
    {                                                                                    \
        TRY_INNER(CFL_matrix_free(&iden));                                               \
        TRY_INNER(LAGraph_Free((void **)&to_new_symbols_map, msg));                      \
        if (rule_routing != NULL) {                                                      \
            for (size_t k = 0; k < new_rules_count; k++) {                               \
                XorFamilyRoutingRuntime *rt = rule_routing[k];                           \
                if (rt != NULL) {                                                        \
                    TRY_INNER(LAGraph_Free((void **)&(rt->resolved_S_operand), msg));    \
                    TRY_INNER(LAGraph_Free((void **)&(rt->resolved_S_target), msg));     \
                    free(rt->resolved_p_ids);                                            \
                    free(rt->masks);                                                     \
                    free(rt);                                                            \
                    rule_routing[k] = NULL;                                              \
                }                                                                        \
            }                                                                            \
            free(rule_routing);                                                          \
            rule_routing = NULL;                                                         \
        }                                                                                \
        TRY_INNER(LAGraph_Free((void **)&new_rules, msg));                               \
        for (size_t i = 0; i < new_symbols_amount; i++) {                                \
            TRY_INNER(CFL_matrix_free(&temp_matrices[i]));                               \
            TRY_INNER(CFL_matrix_free(&delta_matrices[i]));                              \
            TRY_INNER(CFL_matrix_free(&matrices[i]));                                    \
            if (new_adj_matrices != adj_matrices) {                                      \
                TRY_INNER(GrB_free(&new_adj_matrices[i]));                               \
            }                                                                            \
        }                                                                                \
        if (new_adj_matrices != adj_matrices) {                                          \
            TRY_INNER(LAGraph_Free((void **)&new_adj_matrices, msg));                    \
        }                                                                                \
        TRY_INNER(LAGraph_Free((void **)&delta_matrices, msg));                          \
        TRY_INNER(LAGraph_Free((void **)&matrices, msg));                                \
        TRY_INNER(LAGraph_Free((void **)&temp_matrices, msg));                           \
        if (groups != NULL) {                                                            \
            for (size_t gi = 0; gi < groups_count; gi++) {                               \
                free(groups[gi].active_masks);                                           \
                free(groups[gi].p_ids);                                                  \
                free(groups[gi].resolved_p_ids);                                         \
            }                                                                            \
            free(groups);                                                                \
            groups = NULL;                                                               \
        }                                                                                \
    }

#define LG_FREE_ALL                                                                      \
    {                                                                                    \
        LG_FREE_WORK;                                                                    \
    }

#include "LAGraph_CFL_optimized_matrix_opt.h"
#include "LG_internal.h"
#include <LAGraphX.h>

#define ERROR_RULE(msg)                                                                  \
    {                                                                                    \
        LG_ASSERT_MSGF(false, GrB_INVALID_VALUE, "Rule with index %ld is invalid. " msg, \
                       i);                                                               \
    }

#define ADD_TO_MSG(...)                                                                  \
    {                                                                                    \
        if (msg_len == 0) {                                                              \
            msg_len +=                                                                   \
                snprintf(msg, LAGRAPH_MSG_LEN,                                           \
                         "LAGraph failure (file %s, line %d): ", __FILE__, __LINE__);    \
        }                                                                                \
        if (msg_len < LAGRAPH_MSG_LEN) {                                                 \
            msg_len += snprintf(msg + msg_len, LAGRAPH_MSG_LEN - msg_len, __VA_ARGS__);  \
        }                                                                                \
    }

#define ADD_INDEX_TO_ERROR_RULE(rule, i)                                                 \
    {                                                                                    \
        rule.len_indexes_str += snprintf(rule.indexes_str + rule.len_indexes_str,        \
                                         LAGRAPH_MSG_LEN - rule.len_indexes_str,         \
                                         rule.count == 0 ? "%ld" : ", %ld", i);          \
        rule.count++;                                                                    \
    }

#define BENCH_CFL_REACHBILITY false

#if BENCH_CFL_REACHBILITY
    #define IS_ISO(matrix, str)                                                          \
        {                                                                                \
            bool iso_flag;                                                               \
            GrB_Index nnz;                                                               \
            GxB_Matrix_iso(&iso_flag, matrix);                                           \
            GrB_Matrix_nvals(&nnz, matrix);                                              \
            if (!iso_flag && nnz) {                                                      \
                printf("-----ISO ALERT----- (%s)\n", str);                               \
                GxB_print(matrix, 1);                                                    \
                printf("-------------------\n");                                         \
            }                                                                            \
        }

    #define TIMER_START()                                                                \
        {                                                                                \
            start_time = LAGraph_WallClockTime();                                        \
        }

    #define TIMER_STOP(label, accumulator)                                               \
        {                                                                                \
            end_time = LAGraph_WallClockTime();                                          \
            printf("%s %.3fs\n", label, end_time - start_time);                          \
            if (accumulator != NULL) {                                                   \
                *(accumulator) += (end_time - start_time);                               \
            }                                                                            \
        }

    #define IS_ROW(matrix, str)                                                          \
        {                                                                                \
            int32_t orientation;                                                         \
            GrB_get(matrix, &orientation, GrB_STORAGE_ORIENTATION_HINT);                 \
            if (orientation != GrB_ROWMAJOR) {                                           \
                printf("-----NOT A ROW----- (%s)\n", str);                               \
                GxB_print(matrix, 1);                                                    \
                printf("-------------------\n");                                         \
            }                                                                            \
        }

    #define IS_COL(matrix, str)                                                          \
        {                                                                                \
            int32_t orientation;                                                         \
            GrB_get(matrix, &orientation, GrB_STORAGE_ORIENTATION_HINT);                 \
            if (orientation != GrB_COLMAJOR) {                                           \
                printf("-----NOT A COL----- (%s)\n", str);                               \
                GxB_print(matrix, 1);                                                    \
                printf("-------------------\n");                                         \
            }                                                                            \
        }
#else
    #define IS_ISO(matrix, str)
    #define TIMER_START()
    #define TIMER_STOP(label, accumulator)
    #define IS_ROW(matrix, str)
    #define IS_COL(matrix, str)
#endif
// clang-format on

#define OPT_EMPTY (1 << 0)
#define OPT_FORMAT (1 << 1)
#define OPT_LAZY (1 << 2)
#define OPT_BLOCK (1 << 3)

#define TRY(GrB_method)                                                                  \
    {                                                                                    \
        GrB_Info LG_GrB_Info = GrB_method;                                               \
        if (LG_GrB_Info < GrB_SUCCESS) {                                                 \
            fprintf(stderr, "LAGraph failure (file %s, line %d): \n", __FILE__,          \
                    __LINE__);                                                           \
            LG_FREE_ALL;                                                                 \
            return (LG_GrB_Info);                                                        \
        }                                                                                \
    }

// Checks the return value of a GraphBLAS/LAGraph call inside a helper function.
// On failure, logs the error location to stderr, invokes FREE_INNER() to release
// any resources allocated within the current function, and returns the error code.
//
// FREE_INNER() must be defined by the caller before using this macro:
//
//   #define FREE_INNER()       \
//       {                      \
//           LAGraph_Free(&a)   \
//           GrB_free(&M)       \
//       }
//
// Note: use TRY() instead when the function is not a helper (i.e., it has
// its own top-level FREE_ALL cleanup).
#define TRY_INNER(GrB_method)                                                            \
    {                                                                                    \
        GrB_Info LG_GrB_Info = GrB_method;                                               \
        if (LG_GrB_Info < GrB_SUCCESS) {                                                 \
            fprintf(stderr, "LAGraph failure (file %s, line %d): \n", __FILE__,          \
                    __LINE__);                                                           \
            FREE_INNER();                                                                \
            return (LG_GrB_Info);                                                        \
        }                                                                                \
    }

#define TRY_I(GrB_method)                                                                \
    {                                                                                    \
        GrB_Info LG_GrB_Info = GrB_method;                                               \
        if (LG_GrB_Info < GrB_SUCCESS) {                                                 \
            fprintf(stderr,                                                              \
                    "LAGraph failure (file %s, line %d) (Iteration: %d, i: %d): \n",     \
                    __FILE__, __LINE__, iteration, i);                                   \
            return (LG_GrB_Info);                                                        \
        }                                                                                \
    }

typedef struct {
    int32_t index;
    int32_t base_index;
    int32_t count;
} CFL_Symbol;

static int32_t map_lookup_base(int32_t old_id, CFL_Symbol *map, size_t map_size) {
    for (size_t i = 0; i < map_size; i++) {
        int32_t cnt = map[i].count > 0 ? map[i].count : 1;
        if (old_id >= map[i].base_index && old_id < map[i].base_index + cnt) {
            return map[i].index;
        }
    }
    return old_id;
}

// When using the OPT_BLOCK optimization, indexed symbols must be grouped together.
// This produces a mapping: [old_index -> (new_index, base_index, indexed_count)]
//   - new_index:     the index of the symbol in the new numeration
//   - base_index:    the original index of the first symbol in the indexed group
//   - indexed_count: the number of indexed symbols in the group (0 if not indexed)
//
// Example:
//   (0) S   -> (0, 0, 0)  - non-indexed symbol
//   (1) A_0 -> (1, 1, 3)  - indexed group of 3, starting at old index 1
//   (2) A_1 ->              }
//   (3) A_2 ->              } members of the A group
//   (4) B_0 -> (2, 4, 2)  - indexed group of 2, starting at old index 4
//   (5) B_1 ->             } member of the B group
//   (6) C   -> (3, 6, 0)  - non-indexed symbol
//   (7) a   -> (4, 7, 0)  - non-indexed symbol
//
// This mapping is used to build a compact matrix array and to expand
// production rules, both with and without the OPT_BLOCK optimization.
//
// Output: CFL_Symbol **symbols and size_t *size
static GrB_Info get_new_symbols(const LAGraph_rule_EWCNF *rules, size_t rules_count,
                                size_t symbols_amount, CFL_Symbol **symbols, size_t *size,
                                char *msg) {
    *symbols = NULL;
    bool *checked = NULL;

#undef FREE_INNER_WORK
#undef FREE_INNER

#define FREE_INNER_WORK()                                                                \
    {                                                                                    \
        LAGraph_Free((void **)&checked, msg);                                            \
    };

#define FREE_INNER()                                                                     \
    {                                                                                    \
        FREE_INNER_WORK();                                                               \
        LAGraph_Free((void **)symbols, msg);                                             \
    }

    TRY_INNER(LAGraph_Calloc((void **)&checked, symbols_amount, sizeof(bool), msg));
    for (size_t i = 0; i < symbols_amount; i++) {
        checked[i] = false;
    }

    size_t capacity = 1;
    *size = 0;
    TRY_INNER(LAGraph_Calloc((void **)symbols, capacity, sizeof(CFL_Symbol), msg));

    for (size_t i = 0; i < capacity; i++) {
        CFL_Symbol sym = {0};
        (*symbols)[i] = sym;
    }

    for (size_t i = 0; i < rules_count; i++) {
        LAGraph_rule_EWCNF rule = rules[i];

        int32_t prods[3] = {rule.nonterm, rule.prod_A, rule.prod_B};
        int bitmasks[3] = {LAGraph_EWNCF_INDEX_NONTERM, LAGraph_EWNCF_INDEX_PROD_A,
                           LAGraph_EWNCF_INDEX_PROD_B};

        for (size_t j = 0; j < 3; j++) {
            if (prods[j] == -1) {
                continue;
            }

            if (checked[prods[j]])
                continue;

            checked[prods[j]] = true;

            CFL_Symbol sym;
            sym.base_index = prods[j];
            sym.index = *size;
            sym.count = rule.indexed & bitmasks[j] ? rule.indexed_count : 0;

            for (size_t k = sym.base_index; k < sym.base_index + sym.count; k++) {
                checked[k] = true;
            }

            if (*size == capacity) {
                capacity *= 2;
                TRY_INNER(LAGraph_Realloc((void **)symbols, capacity, capacity / 2,
                                          sizeof(CFL_Symbol), msg));
            }

            (*symbols)[(*size)++] = sym;
        }
    }

    for (size_t i = 0; i < symbols_amount; i++) {
        if (checked[i])
            continue;

        if (*size == capacity) {
            capacity *= 2;
            TRY_INNER(LAGraph_Realloc((void **)symbols, capacity, capacity / 2,
                                      sizeof(CFL_Symbol), msg));
        }

        CFL_Symbol sym;
        sym.base_index = i;
        sym.index = *size;
        sym.count = 0;

        (*symbols)[(*size)++] = sym;
        checked[i] = true;
        // printf("Inserted (%ld, %ld, %ld)\n", sym.index, sym.base_index, sym.count);
    }

    FREE_INNER_WORK();

    return GrB_SUCCESS;
}

// Expands indexed grammar rules into a set of concrete rules.
//
//   Before: A_i -> B_i C     (indexed_count = 3)
//           D   -> E F
//   After:  A_0 -> B_0 C
//           A_1 -> B_1 C
//           A_2 -> B_2 C
//           D   -> E F
//
// Output: LAGraph_rule_EWCNF **new_rules and size_t *new_rules_count
static GrB_Info explode_rules(const LAGraph_rule_EWCNF *rules, size_t rules_count,
                              LAGraph_rule_EWCNF **new_rules, size_t *new_rules_count,
                              char *msg) {
    *new_rules = NULL;

#undef FREE_INNER

#define FREE_INNER()                                                                     \
    {                                                                                    \
        LAGraph_Free((void **)new_rules, msg);                                           \
    }

    size_t new_rules_size = 0;
    size_t new_rules_capacity = 1;

    TRY_INNER(LAGraph_Calloc((void **)new_rules, new_rules_capacity,
                             sizeof(LAGraph_rule_EWCNF), msg));

    // explode rules
    for (size_t i_rule = 0; i_rule < rules_count; i_rule++) {
        LAGraph_rule_EWCNF rule = rules[i_rule];

        if (new_rules_size == new_rules_capacity) {
            TRY_INNER(LAGraph_Realloc((void **)new_rules, new_rules_capacity * 2,
                                      new_rules_capacity, sizeof(LAGraph_rule_EWCNF),
                                      msg));
            new_rules_capacity *= 2;
        }

        if (rule.indexed_count == 0) {
            (*new_rules)[new_rules_size++] = rule;
        } else {
            while (new_rules_size + rule.indexed_count >= new_rules_capacity) {
                TRY_INNER(LAGraph_Realloc((void **)new_rules, new_rules_capacity * 2,
                                          new_rules_capacity, sizeof(LAGraph_rule_EWCNF),
                                          msg));
                new_rules_capacity *= 2;
            }

            for (size_t rule_index = 0; rule_index < rule.indexed_count; rule_index++) {
                LAGraph_rule_EWCNF new_rule = rule;
                new_rule.indexed_count = 0;
                new_rule.indexed = 0;
                if (rule.nonterm != -1 && rule.indexed & LAGraph_EWNCF_INDEX_NONTERM) {
                    new_rule.nonterm = rule.nonterm + rule_index;
                }
                if (rule.prod_A != -1 && rule.indexed & LAGraph_EWNCF_INDEX_PROD_A) {
                    new_rule.prod_A = rule.prod_A + rule_index;
                }
                if (rule.prod_B != -1 && rule.indexed & LAGraph_EWNCF_INDEX_PROD_B) {
                    new_rule.prod_B = rule.prod_B + rule_index;
                }

                (*new_rules)[new_rules_size++] = new_rule;
            }
        }
    }

    *new_rules_count = new_rules_size;

    return GrB_SUCCESS;
}

// Splits a CFL_Matrix into an array of GrB_Matrix matrices

// If the matrix is not a horizontal or vertical block vector (i.e., its
// block_type is CELL), the underlying GrB_Matrix is extracted and copied
// into outputs[0]
//
// Otherwise, the matrix split into square sub-matrices of size (graph_size x graph_size)
// Parameters:
//   outputs       - [out] Caller-allocated array of GrB_Matrix to write results into
//                         Must have enough space for all sub-matrices
//   matrix        - [in]  Source CFL_Matrix to split
static GrB_Info split_CFL_matrix(GrB_Matrix *outputs, CFL_Matrix *matrix,
                                 int8_t optimizations) {
    char msg[LAGRAPH_MSG_LEN];
    CFL_Matrix *base_matrix;
    GrB_Index *nrows = NULL, *ncols = NULL;

#undef FREE_INNER

#define FREE_INNER()                                                                     \
    {                                                                                    \
        CFL_matrix_free(&base_matrix);                                                   \
        LAGraph_Free((void **)&nrows, msg);                                              \
        LAGraph_Free((void **)&ncols, msg);                                              \
    }

    if (matrix->block_type == CELL) {
        CFL_Matrix *result;
        TRY_INNER(CFL_matrix_to_base(&result, matrix, optimizations));
        TRY_INNER(GrB_Matrix_dup(outputs, result->base));
        TRY_INNER(CFL_matrix_free(&result));
        return GrB_SUCCESS;
    }

    TRY_INNER(CFL_matrix_to_base(&base_matrix, matrix, optimizations));

    // we can create nrows and ncols array with the same size, it will be mush easier than
    // calculate size of each array :)
    GrB_Index matrices_count = matrix->nrows > matrix->ncols
                                   ? matrix->nrows / matrix->ncols
                                   : matrix->ncols / matrix->nrows;

    TRY_INNER(LAGraph_Calloc((void **)&nrows, matrices_count, sizeof(GrB_Index), msg));
    TRY_INNER(LAGraph_Calloc((void **)&ncols, matrices_count, sizeof(GrB_Index), msg));

    GrB_Index graph_size = matrix->nrows < matrix->ncols ? matrix->nrows : matrix->ncols;
    for (size_t i = 0; i < matrices_count; i++) {
        nrows[i] = graph_size;
        ncols[i] = graph_size;
    }

    GrB_Index m = 0, n = 0;
    if (matrix->block_type == VEC_VERT) {
        m = matrices_count;
        n = 1;
    } else {
        m = 1;
        n = matrices_count;
    }

    TRY_INNER(GxB_Matrix_split(outputs, m, n, nrows, ncols, base_matrix->base, GrB_NULL));

    TRY_INNER(LAGraph_Free((void **)&nrows, msg));
    TRY_INNER(LAGraph_Free((void **)&ncols, msg));
    TRY_INNER(CFL_matrix_free(&base_matrix));

    return GrB_SUCCESS;
}

// Builds the mapping [old_index -> (new_index, base_index, indexed_count)]
// See get_new_symbols() for a detailed description of the mapping format
//
// Parameters:
//   map           - [out] Allocated array of CFL_Symbol. Caller must free
//   size          - [out] Number of entries in map
static GrB_Info get_new_symbols_map(const LAGraph_rule_EWCNF *rules, size_t rules_count,
                                    size_t symbols_amount, CFL_Symbol **map, size_t *size,
                                    char *msg, int8_t optimizations) {
#undef FREE_INNER

#define FREE_INNER()                                                                     \
    {                                                                                    \
        LAGraph_Free((void **)map, msg);                                                 \
    }

    if (optimizations & OPT_BLOCK) {
        TRY_INNER(get_new_symbols(rules, rules_count, symbols_amount, map, size, msg));
    } else {
        *size = symbols_amount;
        TRY_INNER(LAGraph_Calloc((void **)map, symbols_amount, sizeof(CFL_Symbol), msg));
        for (size_t i = 0; i < symbols_amount; i++) {
            CFL_Symbol *sym = &(*map)[i];
            sym->index = i;
            sym->base_index = i;
            sym->count = 0;
        }
    }

    return GrB_SUCCESS;
}

// Builds a new array of adjacency matrices according to the symbol mapping
//
// Parameters:
//   new_adj_matrices_p - [out] Resulting matrix array. Caller must free
//                              (only if OPT_BLOCK is set).
static GrB_Info get_new_adj_matrices(const GrB_Matrix *adj_matrices, CFL_Symbol *map,
                                     GrB_Index map_size, GrB_Matrix **new_adj_matrices_p,
                                     char *msg, int8_t optimizations) {
#undef FREE_INNER

#define FREE_INNER()                                                                     \
    {                                                                                    \
        LAGraph_Free((void **)new_adj_matrices_p, msg);                                  \
    }

    GrB_Index n;
    TRY_INNER(GrB_Matrix_ncols(&n, adj_matrices[0]));

    if (!(optimizations & OPT_BLOCK)) {
        *new_adj_matrices_p = (GrB_Matrix *)adj_matrices;
        return GrB_SUCCESS;
    }

    TRY_INNER(
        LAGraph_Calloc((void **)new_adj_matrices_p, map_size, sizeof(GrB_Matrix), msg));

    for (size_t i = 0; i < map_size; i++) {
        CFL_Symbol sym = map[i];

        if (sym.count == 0) {
            TRY_INNER(
                GrB_Matrix_dup(&(*new_adj_matrices_p)[i], adj_matrices[sym.base_index]));
            continue;
        }

        GrB_Matrix new_col_matrix;
        TRY_INNER(GrB_Matrix_new(&new_col_matrix, GrB_BOOL, n * sym.count, n));
        GrB_Matrix *Tiles = (GrB_Matrix *)adj_matrices + sym.base_index;
        TRY_INNER(GxB_Matrix_concat(new_col_matrix, Tiles, sym.count, 1, GrB_NULL));
        (*new_adj_matrices_p)[i] = new_col_matrix;
    }

    return GrB_SUCCESS;
}

// The mutable, algorithm-owned counterpart of a grammar-supplied `XorFamilyRouting`
// (`spec`). One instance is created per rule that has `xor_routing != NULL`.
//
// Without OPT_BLOCK (`resolved_p_ids == NULL`):
//   Only `spec` is set. Symbol ids are not renumbered in this mode, so algorithm reads
//  `S_operand_base`/`S_target_base`/`active_masks`/`p_ids` straight out of `spec`.
//
// With OPT_BLOCK (`resolved_p_ids != NULL`):
//   Nonterminals get grouped/renumbered before the algorithm runs, so the symbol ids
//   baked into `spec` are stale. This runtime pre-computes their remapped equivalents
//   once, up front:
//     resolved_S_operand[m], resolved_S_target[m] — remapped symbol id of family member
//        `m`, for m in [0, spec->N).
//     masks, resolved_p_ids, masks_count — `spec->active_masks`/`p_ids` after remapping
//        the P-operand ids and deduplicating any (mask, p_id) pairs that collided under
//        the renumbering (owned copies, since `spec`'s arrays must stay untouched).
typedef struct {
    const XorFamilyRouting *spec;
    int32_t *resolved_S_operand;
    int32_t *resolved_S_target;
    int64_t *masks;
    int32_t *resolved_p_ids;
    int64_t masks_count;
} XorFamilyRoutingRuntime;

// Several rules can define XOR families that share the same
// (S_operand_base, S_target_base, S_stride, N) — i.e. they route into the very same
// S_operand/S_target index space, just contributing different (mask, P) terms. Rather
// than evaluating each such rule's family separately, all of them are merged into one
// XorFamilyGroup, so `xor_family_apply_phase_group()` does a single pass over the
// combined term list per group per fixpoint iteration instead of one pass per rule.
//
// active_masks/p_ids/resolved_p_ids are the concatenation of every contributing rule's
// terms (from spec, or from the rule's XorFamilyRoutingRuntime under OPT_BLOCK);
// resolved_S_operand/resolved_S_target are borrowed from any one member's runtime,
// since by construction they are identical across the whole group.
typedef struct {
    int32_t S_operand_base, S_target_base;
    int64_t S_stride;
    int64_t N;
    int64_t total_count;
    int64_t *active_masks;
    int32_t *p_ids;
    int32_t *resolved_p_ids;
    int32_t *resolved_S_operand, *resolved_S_target;
} XorFamilyGroup;

// Builds the "no remapping needed" runtime for a rule's `xor_routing`,
// used when `OPT_BLOCK` is off.
static GrB_Info create_xor_runtime_unblocked(const XorFamilyRouting *spec,
                                           XorFamilyRoutingRuntime **out, char *msg) {
    XorFamilyRoutingRuntime *rt;
    LAGraph_Calloc((void **)&rt, 1, sizeof(XorFamilyRoutingRuntime), msg);
    rt->spec = spec;
    *out = rt;
    return GrB_SUCCESS;
}

// Builds the `OPT_BLOCK` runtime for a rule's `xor_routing`.
// Under `OPT_BLOCK`, indexed nonterminals get grouped into wider block matrices and
// renumbered, so every symbol id that `spec` refers to (the S_operand/S_target family
// members and every P-operand in `p_ids`) has to be looked up through
// `map_lookup_base()` once here.
static GrB_Info create_xor_runtime_blocked(const XorFamilyRouting *spec, CFL_Symbol *map,
                                         size_t map_size, XorFamilyRoutingRuntime **out,
                                         char *msg) {
    XorFamilyRoutingRuntime *rt = NULL;
 
#undef FREE_INNER
#define FREE_INNER()                                                                     \
    {                                                                                    \
        if (rt) {                                                                        \
            LAGraph_Free((void **)&rt->resolved_S_operand, msg);                         \
            LAGraph_Free((void **)&rt->resolved_S_target, msg);                          \
            free(rt->resolved_p_ids);                                                    \
            free(rt->masks);                                                             \
            LAGraph_Free((void **)&rt, msg);                                             \
        }                                                                                \
    }

    TRY_INNER(LAGraph_Calloc((void **)&rt, 1, sizeof(XorFamilyRoutingRuntime), msg));
    rt->spec = spec;

    TRY_INNER(
        LAGraph_Malloc((void **)&rt->resolved_S_operand, spec->N, sizeof(int32_t), msg));
    TRY_INNER(
        LAGraph_Malloc((void **)&rt->resolved_S_target, spec->N, sizeof(int32_t), msg));

    // Resolve each family member's operand/target symbol id once, up front
    for (int64_t m = 0; m < spec->N; m++) {
        rt->resolved_S_operand[m] = map_lookup_base(
            spec->S_operand_base + (int32_t)(m * spec->S_stride), map, map_size);
        rt->resolved_S_target[m] = map_lookup_base(
            spec->S_target_base + (int32_t)(m * spec->S_stride), map, map_size);
    }

    int32_t *tmp_p = malloc(spec->active_masks_count * sizeof(int32_t));
    int64_t *tmp_masks = malloc(spec->active_masks_count * sizeof(int64_t));
    if (!tmp_p || !tmp_masks) {
        free(tmp_p);
        free(tmp_masks);
        FREE_INNER();
        return GrB_OUT_OF_MEMORY;
    }

    // Remap every P-operand id and collapse consecutive duplicate
    // (mask, p_id) pairs that the remapping produced
    int64_t out_n = 0;
    for (int64_t idx_m = 0; idx_m < spec->active_masks_count; idx_m++) {
        int64_t im = spec->active_masks[idx_m];
        int32_t new_p_id = map_lookup_base(spec->p_ids[idx_m], map, map_size);
        if (out_n > 0 && tmp_masks[out_n - 1] == im && tmp_p[out_n - 1] == new_p_id)
            continue;
        tmp_masks[out_n] = im;
        tmp_p[out_n] = new_p_id;
        out_n++;
    }
    rt->resolved_p_ids = tmp_p;
    rt->masks = tmp_masks;
    rt->masks_count = out_n;

    *out = rt;
    return GrB_SUCCESS;
}

// Remaps rule symbol indices according to the symbol mapping
//
// Parameters:
//   new_rules       - [out] Allocated output rule array. Caller must free
//   new_rules_count - [out] Number of rules written to new_rules
//   out_routing     - [out] Allocated array, parallel to new_rules, of
//                     XorFamilyRoutingRuntime* (or NULL per rule).
static GrB_Info get_new_rules(const LAGraph_rule_EWCNF *rules, size_t rules_count,
                              CFL_Symbol *map, size_t map_size,
                              LAGraph_rule_EWCNF **new_rules, size_t *new_rules_count,
                              XorFamilyRoutingRuntime ***out_routing, char *msg,
                              int8_t optimizations) {
    *new_rules_count = 0;
    *out_routing = NULL;
#undef FREE_INNER

#define FREE_INNER()                                                                     \
    {                                                                                    \
        LAGraph_Free((void **)new_rules, msg);                                           \
        LAGraph_Free((void **)out_routing, msg);                                         \
    }

    if (!(optimizations & OPT_BLOCK)) {
        TRY_INNER(explode_rules(rules, rules_count, new_rules, new_rules_count, msg));
        TRY_INNER(LAGraph_Calloc((void **)out_routing, *new_rules_count,
                                 sizeof(XorFamilyRoutingRuntime *), msg));
        for (size_t i = 0; i < *new_rules_count; i++) {
            if ((*new_rules)[i].xor_routing != NULL) {
                TRY_INNER(create_xor_runtime_unblocked((*new_rules)[i].xor_routing,
                                                     &(*out_routing)[i], msg));
            }
        }
        return GrB_SUCCESS;
    }

    TRY_INNER(
        LAGraph_Calloc((void **)new_rules, rules_count, sizeof(LAGraph_rule_EWCNF), msg));
    TRY_INNER(LAGraph_Calloc((void **)out_routing, rules_count,
                             sizeof(XorFamilyRoutingRuntime *), msg));

    for (size_t i = 0; i < rules_count; i++) {
        LAGraph_rule_EWCNF rule = rules[i];
        LAGraph_rule_EWCNF new_rule = rule;

        if (rule.xor_routing != NULL) {
            TRY_INNER(
                create_xor_runtime_blocked(rule.xor_routing, map, map_size, &(*out_routing)[i], msg));
        }

        for (size_t i_sym = 0; i_sym < map_size; i_sym++) {
            CFL_Symbol sym = map[i_sym];

            if (rule.nonterm != -1 && rule.nonterm == sym.base_index) {
                new_rule.nonterm = sym.index;
            }
            if (rule.prod_A != -1 && rule.prod_A == sym.base_index) {
                new_rule.prod_A = sym.index;
            }
            if (rule.prod_B != -1 && rule.prod_B == sym.base_index) {
                new_rule.prod_B = sym.index;
            }
        }

        (*new_rules)[(*new_rules_count)++] = new_rule;
    }

    return GrB_SUCCESS;
}

// Cache entry for memoizing unpacked or modulo-mapped P-operand matrices within a single
// group evaluation pass.
typedef struct {
    int32_t p_id;
    CFL_Matrix *p_base;
    bool occupied;
    bool owned;
} PIdCacheEntry;

// Frees all owned matrices inside the P-operand cache and deallocates the table.
static void p_cache_free(PIdCacheEntry **cache, size_t cap) {
    if (*cache == NULL) {
        return;
    }

    for (size_t i = 0; i < cap; i++) {
        if ((*cache)[i].occupied && (*cache)[i].owned) {
            CFL_matrix_free(&(*cache)[i].p_base);
        }
    }
    free(*cache);
    *cache = NULL;
}


// Returns the base matrix backing a P-operand, memoized per `p_id` in `cache`
// (a simple open-addressed hash table local to one `xor_family_apply_phase_group` call).
// Multiple family members can reference the same P-operand across different masks, and
// under `OPT_BLOCK` the same *un-blocked* base matrix is shared by every block member
// as well.
static GrB_Info get_cached_p_base(int32_t p_id, bool is_blocked, CFL_Matrix *operand,
                                  GrB_Index n, int8_t optimizations, PIdCacheEntry *cache,
                                  size_t cache_capacity, CFL_Matrix **out_p_base) {
    uint32_t magic_multiplier = 2654435769U;
    uint32_t hash = (uint32_t)p_id * magic_multiplier;
    size_t slot_idx = hash & (cache_capacity - 1);

    // Look up p_id in open-addressed slot array
    while (cache[slot_idx].occupied) {
        if (cache[slot_idx].p_id == p_id) {
            *out_p_base = cache[slot_idx].p_base;
            return GrB_SUCCESS;
        }
        slot_idx = (slot_idx + 1) & (cache_capacity - 1);
    }

    CFL_Matrix *p_base_cfl = NULL;
    CFL_Matrix *src_copy = NULL;
    GrB_Index *rows = NULL, *cols = NULL;
    GrB_Scalar one = NULL;
    bool owned = true;

#undef FREE_INNER
#define FREE_INNER()                                                                     \
    {                                                                                    \
        free(rows);                                                                      \
        free(cols);                                                                      \
        GrB_free(&one);                                                                  \
        CFL_matrix_free(&src_copy);                                                      \
        if (owned) CFL_matrix_free(&p_base_cfl);                                         \
    }

    TRY_INNER(CFL_matrix_update(operand));

    if (is_blocked) {
        // Project global coordinates modulo tile size n to construct the local blocked
        // P-matrix
        GrB_Matrix src = NULL;
        if (operand->is_lazy) {
            TRY_INNER(CFL_matrix_to_base(&src_copy, operand, optimizations));
            src = src_copy->base;
        } else {
            src = operand->base;
        }

        TRY_INNER(CFL_matrix_create(&p_base_cfl, n, n));

        GrB_Index nvals = 0;
        TRY_INNER(GrB_Matrix_nvals(&nvals, src));
        if (nvals > 0) {
            rows = (GrB_Index *)malloc(nvals * sizeof(GrB_Index));
            cols = (GrB_Index *)malloc(nvals * sizeof(GrB_Index));
            if (!rows || !cols) {
                FREE_INNER();
                return GrB_OUT_OF_MEMORY;
            }

            TRY_INNER(GrB_Matrix_extractTuples_BOOL(rows, cols, NULL, &nvals, src));
            for (GrB_Index k = 0; k < nvals; k++) {
                rows[k] %= n;
                cols[k] %= n;
            }
            TRY_INNER(GrB_Scalar_new(&one, GrB_BOOL));
            TRY_INNER(GrB_Scalar_setElement_BOOL(one, true));
            TRY_INNER(GxB_Matrix_build_Scalar(p_base_cfl->base, rows, cols, one, nvals));

            free(rows);
            free(cols);
            rows = NULL;
            cols = NULL;
            TRY_INNER(GrB_free(&one));
            TRY_INNER(CFL_matrix_update(p_base_cfl));
        }

        TRY_INNER(CFL_matrix_free(&src_copy));
    } else if (!operand->is_lazy && !(optimizations & OPT_FORMAT)) {
        // Direct reference borrow when non-lazy and format conversion is off
        p_base_cfl = operand;
        owned = false;
    } else {
        TRY_INNER(CFL_matrix_to_base(&p_base_cfl, operand, optimizations));
    }

    cache[slot_idx].p_id = p_id;
    cache[slot_idx].p_base = p_base_cfl;
    cache[slot_idx].owned = owned;
    cache[slot_idx].occupied = true;

    *out_p_base = p_base_cfl;
    return GrB_SUCCESS;
}

// Evaluates one XorFamilyGroup for one phase of the [Variable -> A B] fixpoint step
// (`phase2` picks which side is "delta" this iteration — the same two-phase split the
// ordinary per-rule CFL_mxm calls elsewhere in the main loop use).
//
// A group bundles several (mask, P-operand) terms that all feed the same
// S_operand/S_target family. Handling all masks simultaneously turns what would
// otherwise be N separate matrix multiplies into a single global matrix multiplication
// across all N masks and all N family members at once:
//   1. Early exit: Check if any delta inputs exist before allocating local state.
//   2. Borrow S_operand tiles directly into `S_tiles` without copying if non-lazy.
//   3. Reduce P-operands per mask: Precompute `reduced_p[im]` for all masks `im` in
//      advance.
//   4. Construct super-matrices:
//      a. Concatenate all `reduced_p[im]` tiles horizontally into `P_wide_cfl` (n x N*n).
//      b. Build `S_big_cfl` (N*n x N*n) as an N x N block grid where tile (im, m)
//         holds `S_tiles[im XOR m]`.
//   5. Single matrix multiplication: Perform one wide multiplication
//      `Result_wide = P_wide * S_big` covering all masks simultaneously.
//   6. Direct split: Slice Result_wide_cfl directly into Result_tiles.
//   7. Output write-back: Move tiles to temp_matrices[S_target[m]]. If the target tile
//      is currently empty and non-lazy, transfer matrix ownership directly to bypass
//      CFL_wise.
GrB_Info xor_family_apply_phase_group(XorFamilyGroup *group, bool phase2,
                                      CFL_Matrix **matrices, CFL_Matrix **delta_matrices,
                                      CFL_Matrix **temp_matrices, int8_t optimizations) {
    int64_t N = group->N;
    bool is_blocked = (group->resolved_p_ids != NULL);
    optimizations = optimizations & ~OPT_BLOCK;

    GrB_Matrix S_tiles[N];
    CFL_Matrix *s_cfl[N];
    GrB_Matrix Result_tiles[N];
    CFL_Matrix *reduced_p[N];
    bool reduced_p_owned[N];

    for (int64_t i = 0; i < N; i++) {
        S_tiles[i] = NULL;
        s_cfl[i] = NULL;
        Result_tiles[i] = NULL;
        reduced_p[i] = NULL;
        reduced_p_owned[i] = false;
    }

    PIdCacheEntry *p_cache = NULL;
    size_t cache_capacity = 0;
    CFL_Matrix *Result_wide_cfl = NULL;
    CFL_Matrix *P_wide_cfl = NULL;
    CFL_Matrix *S_big_cfl = NULL;
    GrB_Matrix empty_p_tile = NULL;
    CFL_Matrix *piece = NULL;

#undef FREE_INNER
#define FREE_INNER()                                                                     \
    {                                                                                    \
        CFL_matrix_free(&piece);                                                         \
        if (empty_p_tile != NULL) GrB_free(&empty_p_tile);                               \
        CFL_matrix_free(&S_big_cfl);                                                     \
        CFL_matrix_free(&P_wide_cfl);                                                    \
        CFL_matrix_free(&Result_wide_cfl);                                               \
        for (int64_t i = 0; i < N; i++) {                                                \
            if (reduced_p_owned[i]) CFL_matrix_free(&reduced_p[i]);                      \
            CFL_matrix_free(&s_cfl[i]);                                                  \
            if (Result_tiles[i] != NULL) GrB_free(&Result_tiles[i]);                     \
        }                                                                                \
        p_cache_free(&p_cache, cache_capacity);                                          \
    }

    // 1. Early exit check: Skip execution if no delta matrices contain nonzeros
    bool has_work = false;
    if (!phase2) {
        for (int64_t m = 0; m < N && !has_work; m++) {
            int32_t s_id = is_blocked 
                               ? group->resolved_S_operand[m]
                               : group->S_operand_base + (int32_t)(m * group->S_stride);
            TRY_INNER(CFL_matrix_update(delta_matrices[s_id]));
            has_work = delta_matrices[s_id]->nvals > 0;
        }
    } else {
        for (int64_t k = 0; k < group->total_count && !has_work; k++) {
            int32_t p_id = is_blocked ? group->resolved_p_ids[k] : group->p_ids[k];
            TRY_INNER(CFL_matrix_update(delta_matrices[p_id]));
            has_work = delta_matrices[p_id]->nvals > 0;
        }
    }
    if (!has_work) {
        return GrB_SUCCESS;
    }

    // 2. Gather S_operand tiles once. Non-lazy operands are aliased directly without
    // copies
    for (size_t m = 0; m < N; m++) {
        int32_t s_id = is_blocked
                           ? group->resolved_S_operand[m]
                           : group->S_operand_base + (int32_t)(m * group->S_stride);
        CFL_Matrix *operand = phase2 ? matrices[s_id] : delta_matrices[s_id];
        TRY_INNER(CFL_matrix_update(operand));
        if (!operand->is_lazy) {
            S_tiles[m] = operand->base;
        } else {
            TRY_INNER(CFL_matrix_to_base(&s_cfl[m], operand, optimizations));
            S_tiles[m] = s_cfl[m]->base;
        }
    }

    GrB_Index n;
    TRY_INNER(GrB_Matrix_ncols(&n, S_tiles[0]));

    // Early exit if all gathered S_tiles are empty
    bool any_S = false;
    for (int64_t m = 0; m < N && !any_S; m++) {
        GrB_Index nv;
        TRY_INNER(GrB_Matrix_nvals(&nv, S_tiles[m]));
        any_S = nv > 0;
    }
    if (!any_S) {
        FREE_INNER();
        return GrB_SUCCESS;
    }

    // Allocate P-operand memoization cache
    cache_capacity = 16;
    while (cache_capacity < (size_t)group->total_count * 2) {
        cache_capacity *= 2;
    }
    p_cache = (PIdCacheEntry *)calloc(cache_capacity, sizeof(PIdCacheEntry));
    if (!p_cache) {
        FREE_INNER();
        return GrB_OUT_OF_MEMORY;
    }

    // 3. Reduce P-operands per mask im
    for (int64_t im = 0; im < N; im++) {
        for (size_t idx = 0; idx < group->total_count; idx++) {
            if (group->active_masks[idx] != im) {
                continue;
            }

            int32_t p_id = is_blocked ? group->resolved_p_ids[idx] : group->p_ids[idx];
            CFL_Matrix *operand = phase2 ? delta_matrices[p_id] : matrices[p_id];
            TRY_INNER(CFL_matrix_update(operand));
            if (phase2 && operand->nvals == 0) {
                continue;
            }

            CFL_Matrix *p_base = NULL;
            TRY_INNER(get_cached_p_base(p_id, is_blocked, operand, n, optimizations,
                                        p_cache, cache_capacity, &p_base));
            if (reduced_p[im] == NULL) {
                // Borrow reference directly for single-term masks (bypasses CFL_wise)
                reduced_p[im] = p_base;
                reduced_p_owned[im] = false;
            } else if (!reduced_p_owned[im]) {
                // First reduction step: allocate local sum matrix
                CFL_Matrix *sum = NULL;
                TRY_INNER(CFL_matrix_create(&sum, n, n));
                TRY_INNER(CFL_wise(sum, reduced_p[im], p_base, false, optimizations));
                reduced_p[im] = sum;
                reduced_p_owned[im] = true;
            } else {
                // Accumulate subsequent terms in-place
                TRY_INNER(CFL_wise(reduced_p[im], reduced_p[im], p_base, true, optimizations));
            }
        }
    }

    // Early exit if all reduced P-operands are empty
    bool any_P = false;
    for (int64_t im = 0; im < N; im++) {
        if (reduced_p[im] != NULL) {
            TRY_INNER(CFL_matrix_update(reduced_p[im]));
            if (reduced_p[im]->nvals > 0) {
                any_P = true;
            }
        }
    }

    if (!any_P) {
        FREE_INNER();
        return GrB_SUCCESS;
    }

    // 4. Construct P_wide matrix (n x N*n)
    GrB_Matrix P_wide_tiles[N];
    for (int64_t im = 0; im < N; im++) {
        if (reduced_p[im] != NULL && reduced_p[im]->nvals > 0) {
            P_wide_tiles[im] = reduced_p[im]->base;
        } else {
            if (empty_p_tile == NULL) {
                TRY_INNER(GrB_Matrix_new(&empty_p_tile, GrB_BOOL, n, n));
            }
            P_wide_tiles[im] = empty_p_tile;
        }
    }

    TRY_INNER(CFL_matrix_create(&P_wide_cfl, n, N * n));
    TRY_INNER(GxB_Matrix_concat(P_wide_cfl->base, P_wide_tiles, 1, N, GrB_NULL));
    TRY_INNER(CFL_matrix_update(P_wide_cfl));

    // Construct S_big matrix (N*n x N*n)
    GrB_Matrix S_big_tiles[N * N];
    for (int64_t im = 0; im < N; im++) {
        for (int64_t m = 0; m < N; m++) {
            S_big_tiles[im * N + m] = S_tiles[im ^ m];
        }
    }

    TRY_INNER(CFL_matrix_create(&S_big_cfl, N * n, N * n));
    TRY_INNER(GxB_Matrix_concat(S_big_cfl->base, S_big_tiles, N, N, GrB_NULL));
    TRY_INNER(CFL_matrix_update(S_big_cfl));

    // 5. Single matrix multiplication for all masks
    TRY_INNER(CFL_matrix_create(&Result_wide_cfl, n, N * n));
    TRY_INNER(CFL_mxm(Result_wide_cfl, P_wide_cfl, S_big_cfl, true, false, optimizations));

    // Release intermediate P-cache and big matrices before write-back
    p_cache_free(&p_cache, cache_capacity);
    if (empty_p_tile != NULL) {
        GrB_free(&empty_p_tile);
        empty_p_tile = NULL;
    }
    CFL_matrix_free(&P_wide_cfl);
    CFL_matrix_free(&S_big_cfl);
    for (int64_t im = 0; im < N; im++) {
        if (reduced_p_owned[im]) {
            CFL_matrix_free(&reduced_p[im]);
        }
        reduced_p[im] = NULL;
        reduced_p_owned[im] = false;
    }

    // Early exit if result matrix accumulated no structural nonzeros
    TRY_INNER(CFL_matrix_update(Result_wide_cfl));
    if (Result_wide_cfl->nvals == 0) {
        FREE_INNER();
        return GrB_SUCCESS;
    }

    // 6. Split wide result directly into per-member tiles
    GrB_Index rows_arr[1] = {n};
    GrB_Index cols_arr[N];
    for (size_t i = 0; i < N; i++) {
        cols_arr[i] = n;
    }

    TRY_INNER(GxB_Matrix_split(Result_tiles, 1, N, rows_arr, cols_arr,
                               Result_wide_cfl->base, GrB_NULL));
    TRY_INNER(CFL_matrix_free(&Result_wide_cfl));

    // 7. Write back to temp_matrices[S_target[m]]
    for (size_t m = 0; m < N; m++) {
        int32_t t_id = is_blocked ? group->resolved_S_target[m]
                                  : group->S_target_base + (int32_t)(m * group->S_stride);

        TRY_INNER(CFL_matrix_from_base(&piece, Result_tiles[m]));
        Result_tiles[m] = NULL; // Transfer tile ownership to `piece`

        if (piece->nvals == 0) {
            TRY_INNER(CFL_matrix_free(&piece));
            continue;
        }

        CFL_Matrix *dst = temp_matrices[t_id];
        TRY_INNER(CFL_matrix_update(dst));
        if (dst->nvals == 0 && !dst->is_lazy && dst->nrows == n && dst->ncols == n) {
            // Zero-copy ownership transfer into empty target
            TRY_INNER(CFL_matrix_free(&temp_matrices[t_id]));
            temp_matrices[t_id] = piece;
            piece = NULL;
        } else {
            // Standard in-place union fallback
            TRY_INNER(CFL_wise(dst, dst, piece, true, optimizations));
            TRY_INNER(CFL_matrix_free(&piece));
        }
    }

    FREE_INNER();
    return GrB_SUCCESS;
}

// LAGraph_CFL_reachability_adv: Context-Free Language Reachability Matrix-Based
// Algorithm
//
// This function determines the set of vertex pairs (u, v) in a graph (represented by
// adjacency matrices) such that there is a path from u to v, where the edge labels
// form a word from the language generated by the context-free grammar (represented by
// `rules`).
//
// Terminals and non-terminals are enumerated by integers starting from zero.
// The start non-terminal is the non-terminal with index 0.
//
// Example:
//
// Graph:
// ┌───┐   ┌───┐   ┌───┐   ┌───┐   ┌───┐
// │ 0 ├───► 1 ├───► 2 ├───► 3 ├───► 4 │
// └───┘ a └─┬─┘ a └─▲─┘ b └───┘ b └───┘
//           │       │
//           │ ┌───┐ │
//          a└─► 5 ├─┘b
//             └───┘
//
// Grammar: S -> aSb | ab
//
// There are paths from node [1] to node [3] and from node [1] to node [2] that form
// the word "ab" ([1]-a->[2]-b->[3] and [1]-a->[5]-b->[2]). The word "ab" is in the
// language generated by our context-free grammar, so the pairs (1, 3) and (1, 2) will
// be included in the result.
//
// Note: It doesn't matter how many paths exist from node [A] to node [B] that form a
// word in the language. If at least one path exists, the pair ([A], [B]) will be
// included in the result.
//
// In contrast, the path from node [1] to node [4] forms the word "abb"
// ([1]-a->[2]-b->[3]-b->[4]) and the word "abbb" ([1]-a->[5]-b->[2]-b->[3]-b->[4]).
// The words "aab" and "abbb" are not in the language, so the pair (1, 4) will not be
// included in the result.
//
// With this graph and grammar, we obtain the following results:
// (0, 4) - because there exists a path (0-1-2-3-4) that forms the word "aabb"
// (1, 3) - because there exists a path (1-2-3) that forms "ab"
// (1, 2) - because there exists a path (1-5-2) that forms the word "ab"
// (0, 3) - because there exists a path (0-1-5-2-3) that forms the word "aabb"
GrB_Info LAGraph_CFL_reachability_adv(
    // Output
    GrB_Matrix *outputs, // Array of matrices containing results.
                         // The size of the array must be equal to the count
                         // of symbols (symbols_amount).
                         //
                         // Each matrix is square, with size equal to the number of
                         // vertices in the graph. Matrices are allocated by the
                         // caller, not by this method.
                         //
                         // outputs[k]: (i, j) = true if and only if there is a path
                         // from node i to node j whose edge labels form a word
                         // derivable from the symbol 'k' of the specified CFG.
                         //
                         // Note: output[t], where t is the index of a terminal, will
                         // be an exact copy of adj_matrices[t].
    // Input
    const GrB_Matrix *adj_matrices, // Array of adjacency matrices representing the graph.
                                    // The length of this array is equal to the count of
                                    // symbols (symbols_amount).
                                    //
                                    // Each matrix is square, with size equal to the
                                    // number of vertices in the graph.
                                    //
                                    // adj_matrices[i]: (i, j) == 1 if and only if there
                                    // is an edge between nodes i and j with the label of
                                    // the symbol corresponding to index 'i' (where i is
                                    // in the range [0, symbols_amount - 1]).
                                    //
                                    // Note: adj_matrices[N], where N is the index of a
                                    // nonterminal, must be initialized as an empty square
                                    // matrix of size symbols_amount.
    size_t symbols_amount,          // Count of terminal and nonterminals
    const LAGraph_rule_EWCNF *rules, // The rules of the CFG.
                                     // Warning: now not ready for N -> A rules, where
                                     // is N and A are nonterminals.
    size_t rules_count,              // The total number of rules in the CFG.
    char *msg,                       // Message string for error reporting.
    int8_t optimizations             // Optimizations flags
) {
#undef FREE_INNER

#define FREE_INNER()

    // Declare workspace and clear the msg string, if not NULL
    CFL_Matrix **delta_matrices, **matrices, **temp_matrices;
    CFL_Matrix *iden = NULL;
    GrB_Matrix identity_matrix = NULL;

    // for OPT_BLOCK optimization
    size_t new_symbols_amount = 0;
    GrB_Matrix *new_adj_matrices = NULL;
    LAGraph_rule_EWCNF *new_rules = NULL;
    size_t new_rules_count = 0;
    CFL_Symbol *to_new_symbols_map = NULL;

    XorFamilyRoutingRuntime **rule_routing = NULL;
    XorFamilyGroup *groups = NULL;
    size_t groups_count = 0;

    LG_CLEAR_MSG;
    size_t msg_len = 0; // For error formatting

    TRY(LAGraph_Calloc((void **)&delta_matrices, symbols_amount, sizeof(CFL_Matrix *),
                       msg));
    TRY(LAGraph_Calloc((void **)&matrices, symbols_amount, sizeof(CFL_Matrix *), msg));
    TRY(LAGraph_Calloc((void **)&temp_matrices, symbols_amount, sizeof(CFL_Matrix *),
                       msg));

    LG_ASSERT_MSG(symbols_amount > 0, GrB_INVALID_VALUE,
                  "The number of symbols must be greater than zero.");
    LG_ASSERT_MSG(rules_count > 0, GrB_INVALID_VALUE,
                  "The number of rules must be greater than zero.");
    LG_ASSERT_MSG(outputs != NULL, GrB_NULL_POINTER, "The outputs array cannot be null.");
    LG_ASSERT_MSG(rules != NULL, GrB_NULL_POINTER, "The rules array cannot be null.");
    LG_ASSERT_MSG(adj_matrices != NULL, GrB_NULL_POINTER,
                  "The adjacency matrices array cannot be null.");

    // Find null adjacency matrices
    bool found_null = false;
    for (size_t i = 0; i < symbols_amount; i++) {
        if (adj_matrices[i] != NULL)
            continue;

        if (!found_null) {
            ADD_TO_MSG("Adjacency matrices with these indexes are null: ");
            ADD_TO_MSG("%ld", i);
        } else {
            ADD_TO_MSG(", %ld", i);
        }

        found_null = true;
    }

    if (found_null) {
        LG_FREE_ALL;
        return GrB_NULL_POINTER;
    }

    GrB_Index n;
    TRY(GrB_Matrix_ncols(&n, adj_matrices[0]));

    TRY(get_new_symbols_map(rules, rules_count, symbols_amount, &to_new_symbols_map,
                            &new_symbols_amount, msg, optimizations));
    TRY(get_new_adj_matrices(adj_matrices, to_new_symbols_map, new_symbols_amount,
                             &new_adj_matrices, msg, optimizations));
    TRY(get_new_rules(rules, rules_count, to_new_symbols_map, new_symbols_amount,
                      &new_rules, &new_rules_count, &rule_routing, msg, optimizations));

    // Arrays for processing rules
    size_t eps_rules[new_rules_count], eps_rules_count = 0;   // [Variable -> eps]
    size_t term_rules[new_rules_count], term_rules_count = 0; // [Variable -> term]
    size_t bin_rules[new_rules_count], bin_rules_count = 0;   // [Variable -> AB]

    // Process rules
    typedef struct {
        size_t count;
        size_t len_indexes_str;
        char indexes_str[LAGRAPH_MSG_LEN];
    } rule_error_s;
    rule_error_s term_err = {0};
    rule_error_s nonterm_err = {0};
    rule_error_s invalid_err = {0};
    for (size_t i = 0; i < new_rules_count; i++) {
        LAGraph_rule_EWCNF rule = new_rules[i];

        bool is_rule_eps = rule.prod_A == -1 && rule.prod_B == -1;
        bool is_rule_term = rule.prod_A != -1 && rule.prod_B == -1;
        bool is_rule_bin = rule.prod_A != -1 && rule.prod_B != -1;

        // Check that all rules are well-formed
        if (rule.nonterm < 0 || (size_t)rule.nonterm >= new_symbols_amount) {
            ADD_INDEX_TO_ERROR_RULE(nonterm_err, i);
        }

        // [Variable -> eps]
        if (is_rule_eps) {
            eps_rules[eps_rules_count++] = i;

            continue;
        }

        // [Variable -> term]
        if (is_rule_term) {
            term_rules[term_rules_count++] = i;

            if (rule.prod_A < -1 || (size_t)rule.prod_A >= new_symbols_amount) {
                ADD_INDEX_TO_ERROR_RULE(term_err, i);
            }

            continue;
        }

        // [Variable -> A B]
        if (is_rule_bin) {
            bin_rules[bin_rules_count++] = i;

            if (rule.prod_A < -1 || (size_t)rule.prod_A >= new_symbols_amount ||
                rule.prod_B < -1 || (size_t)rule.prod_B >= new_symbols_amount) {
                ADD_INDEX_TO_ERROR_RULE(nonterm_err, i);
            }

            continue;
        }

        // [Variable -> _ B]
        ADD_INDEX_TO_ERROR_RULE(invalid_err, i);
    }

    if (term_err.count + nonterm_err.count + invalid_err.count > 0) {
        ADD_TO_MSG("Count of invalid rules: %ld.\n",
                   term_err.count + nonterm_err.count + invalid_err.count);

        if (nonterm_err.count > 0) {
            ADD_TO_MSG("Non-terminals must be in range [0, nonterms_count). ");
            ADD_TO_MSG("Indexes of invalid rules: %s\n", nonterm_err.indexes_str)
        }
        if (term_err.count > 0) {
            ADD_TO_MSG("Terminals must be in range [-1, nonterms_count). ");
            ADD_TO_MSG("Indexes of invalid rules: %s\n", term_err.indexes_str)
        }
        if (invalid_err.count > 0) {
            ADD_TO_MSG("[Variable -> _ B] type of rule is not acceptable. ");
            ADD_TO_MSG("Indexes of invalid rules: %.120s\n", invalid_err.indexes_str)
        }

        LG_FREE_ALL;
        return GrB_INVALID_VALUE;
    }

    // Create symbol matrices
    for (size_t i = 0; i < new_symbols_amount; i++) {
        GrB_Index nrows;
        TRY(GrB_Matrix_nrows(&nrows, new_adj_matrices[i]));
        GrB_Index ncols;
        TRY(GrB_Matrix_ncols(&ncols, new_adj_matrices[i]));

        GrB_Matrix new_adj_matrix;
        TRY(GrB_Matrix_dup(&new_adj_matrix, new_adj_matrices[i]));
        TRY(CFL_matrix_from_base(&delta_matrices[i], new_adj_matrix));

        if (optimizations & OPT_LAZY) {
            TRY(CFL_matrix_create_lazy(&matrices[i], nrows, ncols));
        } else {
            TRY(CFL_matrix_create(&matrices[i], nrows, ncols));
        }

        TRY(CFL_matrix_create(&temp_matrices[i], nrows, ncols));
    }

    // Rule [Variable -> term]
    for (size_t i = 0; i < term_rules_count; i++) {
        LAGraph_rule_EWCNF term_rule = new_rules[term_rules[i]];
        CFL_Matrix *nonterm_matrix = delta_matrices[term_rule.nonterm];
        CFL_Matrix *term_matrix = delta_matrices[term_rule.prod_A];

        TRY(CFL_wise(nonterm_matrix, nonterm_matrix, term_matrix, true, optimizations));
    }

    GrB_Vector v_diag;
    TRY(GrB_Vector_new(&v_diag, GrB_BOOL, n));
    TRY(GrB_Vector_assign_BOOL(v_diag, GrB_NULL, GrB_NULL, true, GrB_ALL, n, NULL));
    TRY(GrB_Matrix_diag(&identity_matrix, v_diag, 0));
    TRY(GrB_Vector_free(&v_diag));
    TRY(CFL_matrix_from_base(&iden, identity_matrix));

    // Rule [Variable -> eps]
    for (size_t i = 0; i < eps_rules_count; i++) {
        LAGraph_rule_EWCNF eps_rule = new_rules[eps_rules[i]];
        CFL_Matrix *nonterm_matrix = delta_matrices[eps_rule.nonterm];

        TRY(CFL_wise(nonterm_matrix, nonterm_matrix, iden, true, optimizations));
    }

    // Build `XorFamilyGroups` out of every bin_rule that carries a routing runtime.
    // Rules whose routing has already been resolved to the same
    // (S_operand_base, S_target_base, S_stride, N) are merged into one group.
    for (size_t i = 0; i < bin_rules_count; i++) {
        size_t rule_idx = bin_rules[i];
        XorFamilyRoutingRuntime *rt = rule_routing[rule_idx];
        if (rt == NULL) {
            continue;
        }
        const XorFamilyRouting *spec = rt->spec;

        size_t group_idx = SIZE_MAX;
        for (size_t gi = 0; gi < groups_count; gi++) {
            if (groups[gi].S_operand_base == spec->S_operand_base &&
                groups[gi].S_target_base == spec->S_target_base &&
                groups[gi].S_stride == spec->S_stride && groups[gi].N == spec->N) {
                group_idx = gi;
                break;
            }
        }
        if (group_idx == SIZE_MAX) {
            group_idx = groups_count++;
            groups = realloc(groups, groups_count * sizeof(XorFamilyGroup));
            groups[group_idx] = (XorFamilyGroup){
                .S_operand_base = spec->S_operand_base,
                .S_target_base = spec->S_target_base,
                .S_stride = spec->S_stride,
                .N = spec->N,
                .total_count = 0,
                .active_masks = NULL,
                .p_ids = NULL,
                .resolved_p_ids = NULL,
                .resolved_S_operand = rt->resolved_S_operand,
                .resolved_S_target = rt->resolved_S_target,
            };
        }

        bool is_blocked = (rt->resolved_p_ids != NULL);
        const int64_t *src_masks = is_blocked ? rt->masks : spec->active_masks;
        const int32_t *src_p_ids = is_blocked ? rt->resolved_p_ids : spec->p_ids;
        size_t add_n = (size_t)(is_blocked ? rt->masks_count : spec->active_masks_count);

        size_t old_n = groups[group_idx].total_count;
        groups[group_idx].active_masks =
            realloc(groups[group_idx].active_masks, (old_n + add_n) * sizeof(int64_t));
        groups[group_idx].p_ids = realloc(groups[group_idx].p_ids, (old_n + add_n) * sizeof(int32_t));
        memcpy(groups[group_idx].active_masks + old_n, src_masks, add_n * sizeof(int64_t));
        memcpy(groups[group_idx].p_ids + old_n, src_p_ids, add_n * sizeof(int32_t));

        if (is_blocked) {
            groups[group_idx].resolved_p_ids =
                realloc(groups[group_idx].resolved_p_ids, (old_n + add_n) * sizeof(int32_t));
            memcpy(groups[group_idx].resolved_p_ids + old_n, rt->resolved_p_ids,
                add_n * sizeof(int32_t));
        }
        groups[group_idx].total_count += add_n;
    }

    // Rule [Variable -> Variable1 Variable2]
    double start_time, end_time;
    bool changed = true;
    size_t iteration = 0;
    double mxm1 = 0.0;
    double wise1 = 0.0;
    double mxm2 = 0.0;
    double wise2 = 0.0;
    double rsubt = 0.0;
    while (changed) {
        iteration++;
        changed = false;

#if BENCH_CFL_REACHBILITY
        printf("\n--- ITERATARION %ld ---\n", iteration);
#endif

        for (size_t i = 0; i < new_symbols_amount; i++) {
            TRY_I(CFL_matrix_free(&temp_matrices[i]));
            TRY_I(CFL_matrix_create(&temp_matrices[i], matrices[i]->nrows,
                                    matrices[i]->ncols));
        }

        TIMER_START();
        for (size_t i = 0; i < groups_count; i++) {
            TRY_I(xor_family_apply_phase_group(&groups[i], false, matrices,
                                               delta_matrices, temp_matrices,
                                               optimizations));
        }

        for (size_t i = 0; i < bin_rules_count; i++) {
            LAGraph_rule_EWCNF bin_rule = new_rules[bin_rules[i]];

            if (rule_routing[bin_rules[i]] == NULL) {
                CFL_Matrix *A = matrices[bin_rule.prod_A];
                CFL_Matrix *B = delta_matrices[bin_rule.prod_B];
                CFL_Matrix *C = temp_matrices[bin_rule.nonterm];

                TRY_I(CFL_mxm(C, A, B, true, false, optimizations));
            }
        }
        TIMER_STOP("MXM 1", &mxm1);

        TIMER_START()
        for (size_t i = 0; i < new_symbols_amount; i++) {
            CFL_Matrix *A = delta_matrices[i];
            CFL_Matrix *C = matrices[i];

            TRY_I(CFL_wise(C, C, A, false, optimizations));
        }
        TIMER_STOP("WISE 1", &wise1);

        TIMER_START()
        for (size_t i = 0; i < groups_count; i++) {
            TRY_I(xor_family_apply_phase_group(&groups[i], true, matrices, delta_matrices,
                                               temp_matrices, optimizations));
        }

        for (size_t i = 0; i < bin_rules_count; i++) {
            LAGraph_rule_EWCNF bin_rule = new_rules[bin_rules[i]];

            if (rule_routing[bin_rules[i]] == NULL) {
                CFL_Matrix *A = matrices[bin_rule.prod_B];
                CFL_Matrix *B = delta_matrices[bin_rule.prod_A];
                CFL_Matrix *C = temp_matrices[bin_rule.nonterm];

                TRY_I(CFL_mxm(C, A, B, true, true, optimizations));
            }
        }
        TIMER_STOP("MXM 2", &mxm2);

        // Rule [Variable -> term]
        for (size_t i = 0; i < term_rules_count; i++) {
            LAGraph_rule_EWCNF term_rule = new_rules[term_rules[i]];
            CFL_Matrix *A = temp_matrices[term_rule.nonterm];
            CFL_Matrix *B = delta_matrices[term_rule.prod_A];

            TRY_I(CFL_wise(A, A, B, true, optimizations));
        }

        TIMER_START();
        for (size_t i = 0; i < new_symbols_amount; i++) {
            TRY_I(CFL_dup(delta_matrices[i], temp_matrices[i], optimizations));
        }
        TIMER_STOP("WISE 2 (copy)", &wise2);

        TIMER_START();
        for (size_t i = 0; i < new_symbols_amount; i++) {
            CFL_Matrix *A = matrices[i];
            CFL_Matrix *C = delta_matrices[i];

            TRY_I(CFL_rsub(C, A, optimizations));
        }
        TIMER_STOP("WISE 3 (MASK)", &rsubt);

        size_t new_nnz = 0;
        for (size_t i = 0; i < new_symbols_amount; i++) {
            TRY(CFL_matrix_update(delta_matrices[i]));
            new_nnz += delta_matrices[i]->nvals;
        }

        if (new_nnz != 0) {
            changed = true;
        }
    }

#if BENCH_CFL_REACHBILITY
    printf("MXM1: %.3f, wise1: %.3f, MXM2: %.3f, wise2: %.3f, rsub: %.3f", mxm1, wise1,
           mxm2, wise2, rsubt);
#endif

    // get outputs matrices
    for (size_t i = 0; i < new_symbols_amount; i++) {
        CFL_Symbol sym = to_new_symbols_map[i];
        TRY(split_CFL_matrix(outputs + sym.base_index, matrices[i], optimizations));
    }

    LG_FREE_WORK;
    return GrB_SUCCESS;
}
