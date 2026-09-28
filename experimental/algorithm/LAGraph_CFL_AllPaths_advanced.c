#define LG_FREE_WORK                                                                     \
    {                                                                                    \
        if (outputs_reachability != NULL) {                                              \
            for (size_t i = 0; i < symbols_amount; i++) {                                \
                GrB_free(&outputs_reachability[i]);                                      \
            }                                                                            \
        }                                                                                \
        LAGraph_Free((void **)&outputs_reachability, NULL);                              \
        LAGraph_Free((void **)&T, NULL);                                                 \
        GrB_free(&false_scalar);                                                         \
        GrB_free(&identity_matrix);                                                      \
        GrB_free(&v_diag);                                                               \
        LAGraph_Free((void **)&t_empty_flags, NULL);                                     \
        LAGraph_Free((void **)&eps_rules, NULL);                                         \
        LAGraph_Free((void **)&term_rules, NULL);                                        \
        LAGraph_Free((void **)&bin_rules, NULL);                                         \
        LAGraph_Free((void **)&new_rules, NULL);                                         \
        GrB_free(&AllPaths_monoid);                                                      \
        GrB_free(&bottom_scalar);                                                        \
        GrB_free(&IAllPaths_mult);                                                       \
        GrB_free(&AllPaths_set);                                                         \
        GrB_free(&AllPaths_add);                                                         \
        GrB_free(&rule_theta);                                                           \
        LAGraph_Free((void **)&rule_table, NULL);                                        \
    }

#include "LG_internal.h"
#include <LAGraphX.h>
#include "LAGraph_CFL_AllPaths_internal.h"

// Post-multiplication operation creating path element containing intermediate vertex jx and rule_id
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

// Initializer for terminal or epsilon rules path element
static void set_all_paths(AllPathsElem *z, const AllPathsElem *x,
                          const bool *edge_exist) {
    z->data.single_elem.mid = GrB_INDEX_MAX; // A special value to indicate that this path corresponds to a
                                             // terminal rule (A->t) or an epsilon rule (A->eps)
    z->data.single_elem.rule_count = 0;
    z->data.single_elem.rule_id0 = -1;
    z->data.single_elem.rest.rule_ids_rest = NULL;
    z->n = 1;
}

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

GrB_Info LAGraph_CFL_AllPaths_adv(GrB_Matrix *outputs, GrB_Type *all_paths_ptr_t,
                                  BinaryRuleInfo **out_rule_table,
                                  const GrB_Matrix *adj_matrices, size_t symbols_amount,
                                  const LAGraph_rule_EWCNF *rules, size_t rules_count,
                                  char *msg, int8_t optimizations) {
    LG_CLEAR_MSG;
    size_t msg_len = 0;

    BinaryRuleInfo *rule_table = NULL;
    size_t rule_table_count = 0;
    size_t rule_table_cap = 0;

    GrB_Type AllPaths_type = NULL;

    GrB_Matrix *T = NULL;
    GrB_Scalar false_scalar = NULL;
    GrB_Matrix *outputs_reachability = NULL;
    bool *t_empty_flags = NULL;
    LAGraph_rule_EWCNF *new_rules = NULL;
    size_t new_rules_count = 0;
    size_t *eps_rules = NULL, eps_rules_count = 0;
    size_t *term_rules = NULL, term_rules_count = 0;
    size_t *bin_rules = NULL, bin_rules_count = 0;
    GrB_Matrix identity_matrix = NULL;
    GrB_Vector v_diag = NULL;

#if GxB_IMPLEMENTATION < GxB_VERSION(9, 4, 5)
    return (GrB_NOT_IMPLEMENTED);
#else
    GrB_BinaryOp AllPaths_add = NULL;
    GrB_Monoid AllPaths_monoid = NULL;
    GxB_IndexBinaryOp IAllPaths_mult = NULL;
    GrB_BinaryOp AllPaths_set = NULL;
    GrB_Scalar bottom_scalar = NULL;
    GrB_Scalar rule_theta = NULL;

    GrB_free(all_paths_ptr_t);
    GRB_TRY(
        GxB_Type_new(all_paths_ptr_t, sizeof(AllPathsElem), "AllPathsElem",
                     "typedef struct{GrB_Index mid;uint32_t rule_count;int32_t rule_id0;"
                     "union{int32_t inline_ids[2];int32_t* rule_ids_rest;}rest;}MidEntry;"
                     "typedef struct{size_t n;union{MidEntry single_elem;"
                     "MidEntry* middle;}data;}"
                     "AllPathsElem;"));
    AllPaths_type = *all_paths_ptr_t;

    AllPathsElem bottom = {0};
    GRB_TRY(GrB_Scalar_new(&bottom_scalar, AllPaths_type));
    GRB_TRY(GrB_Scalar_setElement_UDT(bottom_scalar, (void *)(&bottom)));

    GRB_TRY(GrB_BinaryOp_new(&AllPaths_add, (void *)add_all_paths, AllPaths_type,
                             AllPaths_type, AllPaths_type));
    GRB_TRY(GrB_Monoid_new(&AllPaths_monoid, AllPaths_add, (void *)(&bottom)));

    GRB_TRY(GxB_IndexBinaryOp_new(&IAllPaths_mult, (void *)mult_all_paths_post,
                                  AllPaths_type, GrB_BOOL, GrB_BOOL, GrB_INT32,
                                  "mult_all_paths_post", MULT_PATH_POST_INDEX_DEFN));

    GRB_TRY(GrB_BinaryOp_new(&AllPaths_set, (void *)set_all_paths, AllPaths_type,
                             AllPaths_type, GrB_BOOL));

    LG_ASSERT_MSG(outputs != NULL, GrB_NULL_POINTER, "The outputs array cannot be null.");
    LG_CLEAR_MSG;
    msg_len = 0;

    LAGraph_Calloc((void **)&outputs_reachability, symbols_amount, sizeof(GrB_Matrix),
                   msg);
    LG_TRY(LAGraph_CFL_reachability_adv(outputs_reachability, adj_matrices,
                                        symbols_amount, rules, rules_count, msg,
                                        optimizations));

    for (size_t i = 0; i < symbols_amount; i++) {
        GrB_set(outputs_reachability[i], GrB_ROWMAJOR, GrB_STORAGE_ORIENTATION_HINT);
    }

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
                if (rule.nonterm != -1 && rule.indexed & LAGraph_EWNCF_INDEX_NONTERM) {
                    exploded_rule.nonterm = rule.nonterm + rule_index;
                }
                if (rule.prod_A != -1 && rule.indexed & LAGraph_EWNCF_INDEX_PROD_A) {
                    exploded_rule.prod_A = rule.prod_A + rule_index;
                }
                if (rule.prod_B != -1 && rule.indexed & LAGraph_EWNCF_INDEX_PROD_B) {
                    exploded_rule.prod_B = rule.prod_B + rule_index;
                }
                new_rules[nr_idx++] = exploded_rule;
            }
        }
    }

    LG_TRY(LAGraph_Calloc((void **)&T, symbols_amount, sizeof(GrB_Matrix), msg));
    GRB_TRY(GrB_Scalar_new(&false_scalar, GrB_BOOL));
    GRB_TRY(GrB_Scalar_setElement_BOOL(false_scalar, false));
    LG_TRY(LAGraph_Calloc((void **)&t_empty_flags, symbols_amount, sizeof(bool), msg));

    GrB_Index n = 0;
    for (size_t i = 0; i < symbols_amount; i++) {
        if (adj_matrices[i] != NULL) {
            GRB_TRY(GrB_Matrix_ncols(&n, adj_matrices[i]));
            break;
        }
    }

    for (size_t i = 0; i < symbols_amount; i++) {
        GRB_TRY(GrB_Matrix_new(&T[i], AllPaths_type, n, n));
        t_empty_flags[i] = true;
    }

    LG_TRY(LAGraph_Calloc((void **)&eps_rules, new_rules_count, sizeof(size_t), msg));
    LG_TRY(LAGraph_Calloc((void **)&term_rules, new_rules_count, sizeof(size_t), msg));
    LG_TRY(LAGraph_Calloc((void **)&bin_rules, new_rules_count, sizeof(size_t), msg));

    for (size_t i = 0; i < new_rules_count; i++) {
        LAGraph_rule_EWCNF rule = new_rules[i];

        bool is_rule_eps = rule.prod_A == -1 && rule.prod_B == -1;
        bool is_rule_term = rule.prod_A != -1 && rule.prod_B == -1;
        bool is_rule_bin = rule.prod_A != -1 && rule.prod_B != -1;

        if (is_rule_eps) {
            eps_rules[eps_rules_count++] = i;
        } else if (is_rule_term) {
            term_rules[term_rules_count++] = i;
        } else if (is_rule_bin) {
            bin_rules[bin_rules_count++] = i;
        }
    }

    for (size_t i = 0; i < term_rules_count; i++) {
        LAGraph_rule_EWCNF term_rule = new_rules[term_rules[i]];
        if (adj_matrices[term_rule.prod_A] == NULL)
            continue;

        GrB_Index adj_matrix_nnz = 0;
        GRB_TRY(GrB_Matrix_nvals(&adj_matrix_nnz, adj_matrices[term_rule.prod_A]));
        if (adj_matrix_nnz == 0)
            continue;

        GxB_eWiseUnion(T[term_rule.nonterm], GrB_NULL, GrB_NULL, AllPaths_set,
                       T[term_rule.nonterm], bottom_scalar,
                       adj_matrices[term_rule.prod_A], false_scalar, GrB_NULL);
        t_empty_flags[term_rule.nonterm] = false;
    }

    if (eps_rules_count > 0) {
        GRB_TRY(GrB_Vector_new(&v_diag, GrB_BOOL, n));
        GRB_TRY(
            GrB_Vector_assign_BOOL(v_diag, GrB_NULL, GrB_NULL, true, GrB_ALL, n, NULL));
        GRB_TRY(GrB_Matrix_diag(&identity_matrix, v_diag, 0));
        GRB_TRY(GrB_free(&v_diag));

        for (size_t i = 0; i < eps_rules_count; i++) {
            LAGraph_rule_EWCNF eps_rule = new_rules[eps_rules[i]];
            GrB_BinaryOp acc_op =
                t_empty_flags[eps_rule.nonterm] ? GrB_NULL : AllPaths_add;
            GxB_eWiseUnion(T[eps_rule.nonterm], GrB_NULL, acc_op, AllPaths_set,
                           T[eps_rule.nonterm], bottom_scalar, identity_matrix,
                           false_scalar, GrB_NULL);
            t_empty_flags[eps_rule.nonterm] = false;
        }
        GrB_free(&identity_matrix);
    }

    for (size_t i = 0; i < symbols_amount; i++) {
        GrB_Index temp_nvals = 0;
        GRB_TRY(GrB_Matrix_nvals(&temp_nvals, outputs_reachability[i]));
        if (temp_nvals != 0) {
            t_empty_flags[i] = false;
        }
    }

    GRB_TRY(GrB_Scalar_new(&rule_theta, GrB_INT32));

    for (size_t i = 0; i < bin_rules_count; i++) {
        LAGraph_rule_EWCNF bin_rule = new_rules[bin_rules[i]];

        if (bin_rule.xor_routing != NULL) {
            // Handle rules using xor_routing optimization family

            XorFamilyRouting *rt = bin_rule.xor_routing;

            for (int64_t idx_m = 0; idx_m < rt->active_masks_count; idx_m++) {
                int64_t im = rt->active_masks[idx_m];
                int32_t p_id = rt->p_ids[idx_m];

                for (int64_t m = 0; m < rt->N; m++) {
                    int64_t next = m ^ im;
                    int32_t cur_A = rt->S_target_base + (int32_t)(m * rt->S_stride);
                    int32_t cur_pA = p_id;
                    int32_t cur_pB = rt->S_operand_base + (int32_t)(next * rt->S_stride);

                    if (t_empty_flags[cur_pA] || t_empty_flags[cur_pB])
                        continue;

                    int32_t this_rule_id = (int32_t)rule_table_count;
                    LG_TRY(rule_table_push(&rule_table, &rule_table_count,
                                           &rule_table_cap, cur_A, cur_pA, cur_pB));

                    GRB_TRY(GrB_Scalar_setElement_INT32(rule_theta, this_rule_id));

                    GrB_BinaryOp rule_mult;
                    GRB_TRY(
                        GxB_BinaryOp_new_IndexOp(&rule_mult, IAllPaths_mult, rule_theta));

                    GrB_Semiring rule_semiring;
                    GRB_TRY(GrB_Semiring_new(&rule_semiring, AllPaths_monoid, rule_mult));

                    GrB_BinaryOp acc_op = t_empty_flags[cur_A] ? GrB_NULL : AllPaths_add;

                    GRB_TRY(GrB_mxm(T[cur_A], GrB_NULL, acc_op, rule_semiring,
                                    outputs_reachability[cur_pA],
                                    outputs_reachability[cur_pB], GrB_NULL));

                    GrB_free(&rule_semiring);
                    GrB_free(&rule_mult);

                    t_empty_flags[cur_A] = false;
                }
            }
        } else {
            // Standard binary rule processing

            if (t_empty_flags[bin_rule.prod_A] || t_empty_flags[bin_rule.prod_B])
                continue;

            int32_t this_rule_id = (int32_t)rule_table_count;
            LG_TRY(rule_table_push(&rule_table, &rule_table_count, &rule_table_cap,
                            bin_rule.nonterm, bin_rule.prod_A, bin_rule.prod_B));

            GRB_TRY(GrB_Scalar_setElement_INT32(rule_theta, this_rule_id));

            GrB_BinaryOp rule_mult;
            GRB_TRY(GxB_BinaryOp_new_IndexOp(&rule_mult, IAllPaths_mult, rule_theta));

            GrB_Semiring rule_semiring;
            GRB_TRY(GrB_Semiring_new(&rule_semiring, AllPaths_monoid, rule_mult));

            GrB_BinaryOp acc_op = t_empty_flags[bin_rule.nonterm] ? GrB_NULL : AllPaths_add;
            GRB_TRY(GrB_mxm(T[bin_rule.nonterm], GrB_NULL, acc_op, rule_semiring,
                            outputs_reachability[bin_rule.prod_A],
                            outputs_reachability[bin_rule.prod_B], GrB_NULL));

            GrB_free(&rule_semiring);
            GrB_free(&rule_mult);

            t_empty_flags[bin_rule.nonterm] = false;
        }
    }

    if (out_rule_table) {
        *out_rule_table = rule_table;
        rule_table = NULL;
    }

    for (size_t i = 0; i < symbols_amount; i++) {
        outputs[i] = T[i];
        GrB_Matrix_wait(outputs[i], GrB_MATERIALIZE);
    }

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
GrB_Info LAGraph_CFL_AllPaths_adv_free_outputs(GrB_Matrix *outputs,
                                               int64_t nonterms_count,
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
