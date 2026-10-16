//------------------------------------------------------------------------------
// LAGraph_CFL_pattern.h: OPT_Pat = extension of LAGraph_rule_EWCNF and of OPT_BLOCK
//------------------------------------------------------------------------------
//
// OPT_Pat extension for indexed pattern in Context-Free Language Reachability.
//
// NOTATION
//   n  graph size            R  automaton states (1 if none)     n' = R*n
//   N  group size (2^k)      k  number of indexed blocks (i)
//
// STORAGE & IDEA
//   Instead of element-wise operations, OPT_Pat uses block matrix operations in
//   GraphBLAS that respect algebraic group structures (for example, XOR) and automaton
//   state transitions. It relies on Pat_Context for managing precomputed permutation
//   matrices, identity matrices, and caches (sp_cache, rule_cache, fold_cache).
//------------------------------------------------------------------------------

#ifndef LAGRAPH_CFL_PATTERN_H
#define LAGRAPH_CFL_PATTERN_H

#include "LAGraph_CFL_optimized_matrix_opt.h"
#include <GraphBLAS.h>

// Compatibility view used by CFL_Symbol for one Pat pattern.
typedef struct {
    LAGraph_Pat_role role;
    uint32_t masks;
    uint32_t states;
    uint32_t idx_count;
} LAGraph_Pat_pattern;

// Cache entry for fold selectors used in pattern stack folding operations
typedef struct {
    GrB_Index n;  // Block size
    GrB_Index c;  // Number of blocks
    bool vert;    // Orientation flag (true for vertical, false for horizontal)
    GrB_Matrix F; // Precomputed fold selector matrix
} pat_fold_cache_entry;

// Cache slot for rule evaluations and incremental convolution updates
typedef struct {
    const void *key;         // Rule identifier key
    const CFL_Matrix *owner; // Reference to the owner matrix
    GrB_Index owner_nvals;   // Number of values in the owner matrix when cached
    GrB_Matrix matrix;       // Cached result matrix

    // Fields for incremental updates
    GrB_Matrix cay_delta;    // Cayley graph delta matrix computed in the current iteration (Cay(ΔS))
    GrB_Index delta_nvals;   // Number of non-zero elements in ΔS
} pat_rule_cache_slot;

// Cache slot for state permutation matrices
typedef struct {
    const CFL_Matrix *owner; // Reference to the owner matrix
    GrB_Index owner_nvals;   // Number of values in the owner matrix when cached
    GrB_Matrix Sp;           // Cached permuted matrix (S * P_el)
} pat_sp_cache_slot;

// Optimization context structure for indexed pattern
typedef struct Pat_Context {
    GrB_Matrix *P_el;           // Array of permutation matrices for group elements
    GrB_Matrix I_R;             // Identity matrix of size R
    GrB_Matrix I_np;            // Identity matrix of size np
    GrB_Matrix I_N;             // Identity matrix of size N
    GrB_Matrix Pbig;            // Combined big permutation matrix
    GrB_Index N;                // Group size (2^k)
    GrB_Index R;                // Number of automaton states
    GrB_Index np;               // Block dimension (n * R)
    LAGraph_Pat_group group;    // Group operation type (for example, XOR)

    // Caches
    pat_fold_cache_entry *fold_cache;
    size_t fold_cache_count;
    size_t fold_cache_cap;

    pat_rule_cache_slot *rule_cache;
    size_t rule_cache_count;
    size_t rule_cache_cap;

    pat_sp_cache_slot *sp_cache; // Array of size N for state permutation cache slots
} Pat_Context;

// Initializes the pattern optimization context.
//
// Precomputes permutation matrices, identity matrices, and caching structures
// for the specified group and automaton states.
//
// Parameters:
//   ctx   - [out] Pointer to the Pat_Context to initialize.
//   N     - [in]  Group size.
//   R     - [in]  Number of automaton states.
//   np    - [in]  Block dimension (n * R).
//   g     - [in]  Group operation type (for example, XOR).
//
// Returns:
//   GrB_Info GraphBLAS execution status.
GrB_Info CFL_Pat_context_init(Pat_Context *ctx, GrB_Index N, GrB_Index R, GrB_Index np,
                             LAGraph_Pat_group g);

// Frees resources associated with the pattern optimization context.
//
// Clears all allocated matrices, caches, and internal arrays within the context.
//
// Parameters:
//   ctx   - [in] Pointer to the Pat_Context.
void CFL_Pat_context_free(Pat_Context *ctx);

// Performs block matrix multiplication for pattern rules (OPT_Pat).
//
// Called from matrix_mxm_block when OPT_BLOCK and OPT_Pat optimizations are active.
// Computes the product according to the rule kind (scale, right, left, conv, project).
//
// Parameters:
//   output        - [out] Resulting matrix.
//   first         - [in]  First operand.
//   second        - [in]  Second operand.
//   accum         - [in]  Accumulate flag.
//   swap          - [in]  Operand swap flag.
//   optimizations - [in]  Bitmask of enabled optimizations.
//   pat           - [in]  Patily rule descriptor.
//   ctx           - [in]  Patily optimization context.
//
// Returns:
//   GrB_Info GraphBLAS execution status.
GrB_Info CFL_Pat_matrix_mxm(CFL_Matrix *output, CFL_Matrix *first, CFL_Matrix *second,
                           bool accum, bool swap, int8_t optimizations,
                           const LAGraph_rule_Pat *pat, const Pat_Context *ctx);

// Applies epsilon rules for pattern.
//
// Fills blocks of the reachability delta matrix for symbol S according to epsilon rule.
//
// Parameters:
//   delta_S       - [out] Reachability delta matrix for S.
//   pat           - [in]  Patily rule descriptor.
//   n             - [in]  Base graph size.
//   optimizations - [in]  Bitmask of enabled optimizations.
//
// Returns:
//   GrB_Info GraphBLAS execution status.
GrB_Info CFL_Pat_eps(CFL_Matrix *delta_S, const LAGraph_rule_Pat *pat, GrB_Index n,
                    int8_t optimizations);

// Computes the total span of symbols for a specific rule role.
//
// Parameters:
//   pat         - [in] Patily rule descriptor.
//   role_index  - [in] Index of the role within the rule.
//
// Returns:
//   int64_t Total span size.
int64_t CFL_Pat_span(const LAGraph_rule_Pat *pat, int role_index);

// Checks the validity of a pattern rule descriptor.
//
// Validates masks, states, indices, and role types.
//
// Parameters:
//   pat             - [in] Patily rule descriptor.
//   symbols_amount  - [in] Total number of symbols in the grammar.
//   msg             - [out] Buffer to write an error message if verification fails.
//
// Returns:
//   GrB_Info GraphBLAS execution status.
GrB_Info CFL_Pat_check(const LAGraph_rule_Pat *pat, size_t symbols_amount, char *msg);

// Computes the expected shape (dimensions) of a matrix for a pattern.
//
// Parameters:
//   pat     - [in]  Patily descriptor.
//   n       - [in]  Base graph size.
//   nrows   - [out] Pointer to store the number of rows.
//   ncols   - [out] Pointer to store the number of columns.
//
// Returns:
//   GrB_Info GraphBLAS execution status.
GrB_Info CFL_Pat_shape(const LAGraph_Pat_pattern *pat, GrB_Index n, GrB_Index *nrows,
                          GrB_Index *ncols);

// Splits a large pattern matrix into individual matrix blocks (n x n).
//
// Parameters:
//   outputs       - [out] Array of resulting matrices.
//   matrix        - [in]  Source pattern matrix.
//   pat           - [in]  Patily descriptor.
//   n             - [in]  Base graph size.
//   optimizations - [in]  Bitmask of enabled optimizations.
//
// Returns:
//   GrB_Info GraphBLAS execution status.
GrB_Info CFL_Pat_split(GrB_Matrix *outputs, CFL_Matrix *matrix,
                      const LAGraph_Pat_pattern *pat, GrB_Index n, int8_t optimizations);

#endif // LAGRAPH_CFL_PATTERN_H
