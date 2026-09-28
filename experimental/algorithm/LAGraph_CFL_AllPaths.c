#define LG_FREE_WORK                                                                     \
    {                                                                                    \
        if (mode == 0) {                                                                 \
            if (outputs_reachability != NULL) {                                          \
                for (int64_t i = 0; i < nonterms_count; i++) {                           \
                    GrB_free(&outputs_reachability[i]);                                  \
                }                                                                        \
                \            
                                                                    \
            }                                                                            \
            LAGraph_Free((void **)&outputs_reachability, NULL);                          \
            LAGraph_Free((void **)&T, NULL);                                             \
            GrB_free(&false_scalar);                                                     \
            GrB_free(&identity_matrix);                                                  \
            GrB_free(&v_diag);                                                           \
            LAGraph_Free((void **)&t_empty_flags, NULL);                                 \
            LAGraph_Free((void **)&eps_rules, NULL);                                     \
            LAGraph_Free((void **)&term_rules, NULL);                                    \
            LAGraph_Free((void **)&bin_rules, NULL);                                     \
            LAGraph_Free((void **)&rule_table, NULL);                                    \
        }                                                                                \
        GrB_free(&AllPaths_semiring);                                                    \
        GrB_free(&AllPaths_monoid);                                                      \
        GrB_free(&AllPaths_monoid_get_nvals);                                            \
        GrB_free(&bottom_scalar);                                                        \
        GrB_free(&IAllPaths_mult);                                                       \
        GrB_free(&AllPaths_set);                                                         \
        GrB_free(&AllPaths_mult);                                                        \
        GrB_free(&AllPaths_add);                                                         \
        GrB_free(&AllPaths_add_get_nvals);                                               \
        GrB_free(&Theta);                                                                \
        GrB_free(&rule_theta);                                                           \
    }

#define ADD_TO_MSG_ALL_PATHS(...)                                                        \
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

#include "LG_internal.h"
#include <LAGraphX.h>
#include "LAGraph_CFL_AllPaths_internal.h"

// Index binary multiplication operator for CFPQ core mode (mode 1)
// Constructs a path element tracking the intermediate matrix column index jx
static void mult_all_paths(AllPathsElem *z, const AllPathsElem *x, GrB_Index ix,
                           GrB_Index jx, const AllPathsElem *y, GrB_Index iy,
                           GrB_Index jy, const void *theta) {
    z->data.single_elem.mid = jx;
    z->data.single_elem.rule_count = 0;
    z->data.single_elem.rule_id0 = -1;
    z->data.single_elem.rest.rule_ids_rest = NULL;
    z->n = 1;
}

// Index binary multiplication operator for postprocessing mode (mode 0)
// Constructs a path element tracking intermediate node jx and binary rule ID from theta
static void mult_all_paths_post(AllPathsElem *z, const void *x, GrB_Index ix,
                                GrB_Index jx, const void *y, GrB_Index iy, GrB_Index jy,
                                const void *theta) {
    int32_t rule_id = *(const int32_t *)theta;
    z->data.single_elem.mid = jx;
    z->data.single_elem.rule_count = 1;
    z->data.single_elem.rule_id0 = rule_id;
    z->data.single_elem.rest.rule_ids_rest = NULL;
    z->n = 1;
}

// Binary operator callback for initializing base-case paths (terminal and epsilon transitions)
static void set_all_paths(AllPathsElem *z, const AllPathsElem *x,
                          const bool *edge_exist) {
    z->data.single_elem.mid =
        GrB_INDEX_MAX; // A special value to indicate that this path corresponds to a
                       // terminal rule (A->t) or an epsilon rule (A->eps)
    z->data.single_elem.rule_count = 0;
    z->data.single_elem.rule_id0 = -1;
    z->data.single_elem.rest.rule_ids_rest = NULL;
    z->n = 1;
}

#define MULT_PATH_INDEX_DEFN                                                             \
    "static void mult_all_paths(AllPathsElem *z, \n"                                     \
    "                     const AllPathsElem *x, GrB_Index ix, GrB_Index jx, \n"         \
    "                     const AllPathsElem *y, GrB_Index iy, GrB_Index jy, \n"         \
    "                     const void *theta) \n"                                         \
    "{ \n"                                                                               \
    "  z->data.single_elem.mid = jx; \n"                                                 \
    "  z->data.single_elem.rule_count = 0; \n"                                           \
    "  z->data.single_elem.rule_id0 = -1; \n"                                            \
    "  z->data.single_elem.rest.rule_ids_rest = NULL; \n"                                \
    "  z->n = 1; \n"                                                                     \
    "}"

#define MULT_PATH_POST_INDEX_DEFN                                                        \
    "static void mult_all_paths_post(AllPathsElem *z, \n"                                \
    "                     const void *x, GrB_Index ix, GrB_Index jx, \n"                 \
    "                     const void *y, GrB_Index iy, GrB_Index jy, \n"                 \
    "                     const void *theta) \n"                                         \
    "{ \n"                                                                               \
    "  int32_t rule_id = *(const int32_t *)theta; \n"                                    \
    "  z->data.single_elem.mid = jx; \n"                                                 \
    "  z->data.single_elem.rule_count = 1; \n"                                           \
    "  z->data.single_elem.rule_id0 = rule_id; \n"                                       \
    "  z->data.single_elem.rest.rule_ids_rest = NULL; \n"                                \
    "  z->n = 1; \n"                                                                     \
    "}"

// Adding the count of all internal vertices in a reduction
static void add_get_nvals_all_paths(AllPathsElem *z, const AllPathsElem *x,
                                    const AllPathsElem *y) {
    z->n = x->n + y->n;
}

// Made global so that the get_nvals_all_paths matches the GrB_Matrix_nvals signature
static GrB_Type AllPaths_type = NULL;
static GrB_Monoid AllPaths_monoid_get_nvals = NULL;

// A function that replaces GrB_Matrix_nvals in Reachability to check if new vertices have
// been added to the matrix.
static GrB_Info get_nvals_all_paths(GrB_Index *nvals, const GrB_Matrix A) {
    GrB_Scalar s = NULL;
    GrB_Scalar_new(&s, AllPaths_type);
    GrB_Info info = GrB_reduce(s, NULL, AllPaths_monoid_get_nvals, A, NULL);

    if (info != GrB_SUCCESS) {
        GrB_free(&s);
        return info;
    }

    AllPathsElem result = {0};
    info = GrB_Scalar_extractElement_UDT(&result, s);
    if (info == GrB_NO_VALUE) {
        result.n = 0;
    } else if (info != GrB_SUCCESS) {
        GrB_free(&s);
        return info;
    }

    *nvals = result.n;
    GrB_free(&s);
    return GrB_SUCCESS;
}

GrB_Info LAGraph_CFL_AllPaths(
    // Output
    GrB_Matrix *outputs, // Array of matrices containing results.
                         // The size of the array must be equal to nonterms_count.
                         // Matrix elements are ordered arrays of intermediate vertices
                         // type AllPathsElem. Before free outputs[k], you need to free
                         // arrays from all matrix elements. For all values of M from the
                         // array of the matrix element outputs[k] on the I row of the J
                         // column: There are paths from I to M by nonterminal N1 and from
                         // M to J by nonterminal N2, and A->N1 N2 where outputs[k]
                         // corresponds to nonterminal A. GrB_INDEX_MAX in the array is a
                         // special value for A->eps and A->t.
    // AllPaths type - elements of the output matrices.
    GrB_Type *all_paths_ptr_t, // Pass a pointer to GrB_Type.
    BinaryRuleInfo **out_rule_table, // Pointer to store output binary rule metadata table.
    // Input
    const GrB_Matrix *adj_matrices, // Array of adjacency matrices representing the graph.
                                    // The length of this array is equal to the count of
                                    // terminals (terms_count).
                                    //
                                    // adj_matrices[t]: (i, j) == 1 if and only if there
                                    // is an edge between nodes i and j with the label of
                                    // the terminal corresponding to index 't' (where t is
                                    // in the range [0, terms_count - 1]).
    int64_t terms_count,            // The total number of terminal symbols in the CFG.
    int64_t nonterms_count, // The total number of non-terminal symbols in the CFG.
    const LAGraph_rule_WCNF *rules, // The rules of the CFG.
    int64_t rules_count,            // The total number of rules in the CFG.
    char *msg,                      // Message string for error reporting.
    int8_t mode // mode = 0 - postprocessing(prefer), mode = 1 - CFPQ Core
) {
    LG_CLEAR_MSG;
    size_t msg_len = 0; // For error formatting
    GrB_Matrix *T = NULL;
    GrB_Scalar false_scalar = NULL;
    GrB_Matrix *outputs_reachability = NULL;
    bool *t_empty_flags = NULL; // t_empty_flags[i] == true <=> T[i] is empty
    // Arrays for processing rules
    size_t *eps_rules = NULL, eps_rules_count = 0;   // [Variable -> eps]
    size_t *term_rules = NULL, term_rules_count = 0; // [Variable -> term]
    size_t *bin_rules = NULL, bin_rules_count = 0;   // [Variable -> AB]

    BinaryRuleInfo *rule_table = NULL;
    size_t rule_table_count = 0;
    size_t rule_table_cap = 0;

    GrB_Matrix identity_matrix = NULL;
    GrB_Vector v_diag = NULL;

#if GxB_IMPLEMENTATION < GxB_VERSION(9, 4, 5)
    return (GrB_NOT_IMPLEMENTED);
#else
    // Create a semiring for the CFPQ core and postprocessing modes
    GrB_BinaryOp AllPaths_add = NULL;
    GrB_BinaryOp AllPaths_add_get_nvals = NULL;
    GrB_Monoid AllPaths_monoid = NULL;
    GxB_IndexBinaryOp IAllPaths_mult = NULL;
    GrB_BinaryOp AllPaths_mult = NULL;
    GrB_Semiring AllPaths_semiring = NULL;
    GrB_BinaryOp AllPaths_set = NULL;
    GrB_Scalar Theta = NULL;
    GrB_Scalar bottom_scalar = NULL;
    GrB_Scalar rule_theta = NULL;

    GrB_free(all_paths_ptr_t);
    GRB_TRY(GrB_Type_new(all_paths_ptr_t, sizeof(AllPathsElem)));
    AllPaths_type = *all_paths_ptr_t;

    AllPathsElem bottom = {0};
    GRB_TRY(GrB_Scalar_new(&bottom_scalar, AllPaths_type));
    GRB_TRY(GrB_Scalar_setElement_UDT(bottom_scalar, (void *)(&bottom)));

    GRB_TRY(GrB_BinaryOp_new(&AllPaths_add, (void *)add_all_paths, AllPaths_type,
                             AllPaths_type, AllPaths_type));

    GRB_TRY(GrB_Monoid_new(&AllPaths_monoid, AllPaths_add, (void *)(&bottom)));
    // CFPQ core
    if (mode == 1) {
        GRB_TRY(GxB_IndexBinaryOp_new(&IAllPaths_mult, (void *)mult_all_paths,
                                      AllPaths_type, AllPaths_type, AllPaths_type,
                                      GrB_BOOL, "mult_all_paths", MULT_PATH_INDEX_DEFN));

        GRB_TRY(GrB_Scalar_new(&Theta, GrB_BOOL));
        GRB_TRY(GrB_Scalar_setElement_BOOL(Theta, false));

        GRB_TRY(GxB_BinaryOp_new_IndexOp(&AllPaths_mult, IAllPaths_mult, Theta));

        GRB_TRY(GrB_Semiring_new(&AllPaths_semiring, AllPaths_monoid, AllPaths_mult));
    }
    // postprocessing
    else if (mode == 0) {
        GRB_TRY(GxB_IndexBinaryOp_new(&IAllPaths_mult, (void *)mult_all_paths_post,
                                      AllPaths_type, GrB_BOOL, GrB_BOOL, GrB_INT32,
                                      "mult_all_paths_post", MULT_PATH_POST_INDEX_DEFN));
        GRB_TRY(GrB_Scalar_new(&rule_theta, GrB_INT32));
    } else {
        ADD_TO_MSG_ALL_PATHS("Mode must be 0(postprocessing) or 1(CFPQ Core)");
        return GrB_INVALID_VALUE;
    }

    GRB_TRY(GrB_BinaryOp_new(&AllPaths_set, (void *)set_all_paths, AllPaths_type,
                             AllPaths_type, GrB_BOOL));

    GRB_TRY(GrB_BinaryOp_new(&AllPaths_add_get_nvals, (void *)add_get_nvals_all_paths,
                             AllPaths_type, AllPaths_type, AllPaths_type));

    GRB_TRY(GrB_Monoid_new(&AllPaths_monoid_get_nvals, AllPaths_add_get_nvals,
                           (void *)(&bottom)));

    CFL_Semiring semiring = {.type = AllPaths_type,
                             .semiring = AllPaths_semiring,
                             .add = AllPaths_add,
                             .mult = AllPaths_mult,
                             .init_path = AllPaths_set,
                             .bottom_scalar = bottom_scalar,
                             .get_nvals = get_nvals_all_paths};

    // CFPQ core mode
    if (mode == 1) {
        // Rule provenance isn't tracked in this mode
        if (out_rule_table) {
            *out_rule_table = NULL;
        }
        LG_TRY(LAGraph_CFPQ_core(outputs, adj_matrices, terms_count, nonterms_count,
                                 rules, rules_count, &semiring, msg));
    }
    // postprocessing mode
    else if (mode == 0) {
        LG_ASSERT_MSG(outputs != NULL, GrB_NULL_POINTER,
                      "The outputs array cannot be null.");
        LG_CLEAR_MSG;
        msg_len = 0;

        LAGraph_Calloc((void **)&outputs_reachability, nonterms_count, sizeof(GrB_Matrix),
                       msg);
        LG_TRY(LAGraph_CFL_reachability(outputs_reachability, adj_matrices, terms_count,
                                        nonterms_count, rules, rules_count, msg));

        LG_TRY(LAGraph_Calloc((void **)&T, nonterms_count, sizeof(GrB_Matrix), msg));
        GRB_TRY(GrB_Scalar_new(&false_scalar, GrB_BOOL));
        GRB_TRY(GrB_Scalar_setElement_BOOL(false_scalar, false));
        LG_TRY(
            LAGraph_Calloc((void **)&t_empty_flags, nonterms_count, sizeof(bool), msg));
        GrB_Index n;
        GRB_TRY(GrB_Matrix_ncols(&n, adj_matrices[0]));

        // Create nonterms matrices
        for (int64_t i = 0; i < nonterms_count; i++) {
            GRB_TRY(GrB_Matrix_new(&T[i], semiring.type, n, n));
            t_empty_flags[i] = true;
        }

        LG_TRY(LAGraph_Calloc((void **)&eps_rules, rules_count, sizeof(size_t), msg));
        LG_TRY(LAGraph_Calloc((void **)&term_rules, rules_count, sizeof(size_t), msg));
        LG_TRY(LAGraph_Calloc((void **)&bin_rules, rules_count, sizeof(size_t), msg));

        // Classify rules into three types: [Variable -> eps], [Variable -> term], and
        // [Variable -> A B]
        for (int64_t i = 0; i < rules_count; i++) {
            LAGraph_rule_WCNF rule = rules[i];
            bool is_rule_eps = rule.prod_A == -1 && rule.prod_B == -1;
            bool is_rule_term = rule.prod_A != -1 && rule.prod_B == -1;
            bool is_rule_bin = rule.prod_A != -1 && rule.prod_B != -1;
            // [Variable -> eps]
            if (is_rule_eps) {
                eps_rules[eps_rules_count++] = i;
                continue;
            }
            // [Variable -> term]
            if (is_rule_term) {
                term_rules[term_rules_count++] = i;
                continue;
            }
            // [Variable -> A B]
            if (is_rule_bin) {
                bin_rules[bin_rules_count++] = i;
                continue;
            }
        }

        // Rule [Variable -> term]
        for (int64_t i = 0; i < term_rules_count; i++) {
            LAGraph_rule_WCNF term_rule = rules[term_rules[i]];
            GrB_Index adj_matrix_nnz = 0;
            GRB_TRY(GrB_Matrix_nvals(&adj_matrix_nnz, adj_matrices[term_rule.prod_A]));
            if (adj_matrix_nnz == 0) {
                continue;
            }
            GxB_eWiseUnion(T[term_rule.nonterm], GrB_NULL, GrB_NULL, semiring.init_path,
                           T[term_rule.nonterm], semiring.bottom_scalar,
                           adj_matrices[term_rule.prod_A], false_scalar, GrB_NULL);

            t_empty_flags[term_rule.nonterm] = false;
        }

        GRB_TRY(GrB_Vector_new(&v_diag, GrB_BOOL, n));
        GRB_TRY(
            GrB_Vector_assign_BOOL(v_diag, GrB_NULL, GrB_NULL, true, GrB_ALL, n, NULL));
        GRB_TRY(GrB_Matrix_diag(&identity_matrix, v_diag, 0));
        GRB_TRY(GrB_free(&v_diag));

        // Rule [Variable -> eps]
        for (int64_t i = 0; i < eps_rules_count; i++) {
            LAGraph_rule_WCNF eps_rule = rules[eps_rules[i]];
            GrB_BinaryOp acc_op =
                t_empty_flags[eps_rule.nonterm] ? GrB_NULL : semiring.add;
            GxB_eWiseUnion(T[eps_rule.nonterm], GrB_NULL, acc_op, semiring.init_path,
                           T[eps_rule.nonterm], semiring.bottom_scalar, identity_matrix,
                           false_scalar, GrB_NULL);

            t_empty_flags[eps_rule.nonterm] = false;
        }
        GrB_free(&identity_matrix);

        // Marking dont empty matrices after transitive closure
        for (int64_t i = 0; i < nonterms_count; i++) {
            GrB_Index temp_nvals = 0;
            GrB_Matrix_nvals(&temp_nvals, outputs_reachability[i]);
            if (temp_nvals != 0) {
                t_empty_flags[i] = false;
            }
        }

        // Rule [Variable -> A B]
        for (int64_t i = 0; i < bin_rules_count; i++) {
            LAGraph_rule_WCNF bin_rule = rules[bin_rules[i]];

            // If one of matrices is empty then their product will be empty
            if (t_empty_flags[bin_rule.prod_A] || t_empty_flags[bin_rule.prod_B])
                continue;

            int32_t this_rule_id = (int32_t)rule_table_count;
            LG_TRY(rule_table_push(&rule_table, &rule_table_count, &rule_table_cap,
                                   (int32_t)bin_rule.nonterm, (int32_t)bin_rule.prod_A,
                                   (int32_t)bin_rule.prod_B));

            GRB_TRY(GrB_Scalar_setElement_INT32(rule_theta, this_rule_id));

            GrB_BinaryOp rule_mult;
            GRB_TRY(GxB_BinaryOp_new_IndexOp(&rule_mult, IAllPaths_mult, rule_theta));

            GrB_Semiring rule_semiring;
            GRB_TRY(GrB_Semiring_new(&rule_semiring, AllPaths_monoid, rule_mult));

            GrB_BinaryOp acc_op =
                t_empty_flags[bin_rule.nonterm] ? GrB_NULL : semiring.add;
            GRB_TRY(GrB_mxm(T[bin_rule.nonterm], GrB_NULL, acc_op, rule_semiring,
                            outputs_reachability[bin_rule.prod_A],
                            outputs_reachability[bin_rule.prod_B], GrB_NULL))

            GrB_free(&rule_semiring);
            GrB_free(&rule_mult);
        }

        if (out_rule_table) {
            *out_rule_table = rule_table;
            rule_table = NULL;
        }

        for (size_t i = 0; i < nonterms_count; i++) {
            outputs[i] = T[i];
            GrB_Matrix_wait(outputs[i], GrB_MATERIALIZE);
        }
    } // End of postprocessing mode
    LG_FREE_WORK;
    return GrB_SUCCESS;
#endif
}

// Helper function to free the output matrix of LAGraph_CFL_AllPaths, which contains
// elements of type AllPathsElem with dynamically allocated arrays of intermediate
// vertices.
static void free_AllPaths_matrix(GrB_Matrix *ptr_output) {
    GxB_Iterator iterator;
    GxB_Iterator_new(&iterator);
    GrB_Info info = GxB_Matrix_Iterator_attach(iterator, *ptr_output, NULL);
    info = GxB_Matrix_Iterator_seek(iterator, 0);
    AllPathsElem val;

    while (info != GxB_EXHAUSTED) {
        GxB_Iterator_get_UDT(iterator, (void *)&val);
        free_all_paths_elem_internal(&val);
        info = GxB_Matrix_Iterator_next(iterator);
    }

    GrB_free(&iterator);
    GrB_free(ptr_output);
}

// Free outputs and all_paths_ptr_t after you have finished working with the output
// matrices from LAGraph_CFL_AllPaths. do outputs = NULL, all_paths_ptr_t = NULL after
// LAGraph_CFL_AllPaths_free_outputs
GrB_Info LAGraph_CFL_AllPaths_free_outputs(GrB_Matrix *outputs, int64_t nonterms_count,
                                           GrB_Type *all_paths_ptr_t) {
#if GxB_IMPLEMENTATION < GxB_VERSION(9, 4, 5)
    return (GrB_NOT_IMPLEMENTED);
#else
    if (outputs) {
        for (size_t i = 0; i < nonterms_count; i++) {
            if (outputs[i] == NULL)
                continue;
            free_AllPaths_matrix(&outputs[i]);
            outputs[i] = NULL;
        }
        free(outputs);
    }
    GrB_free(all_paths_ptr_t);
    return GrB_SUCCESS;
#endif
}
