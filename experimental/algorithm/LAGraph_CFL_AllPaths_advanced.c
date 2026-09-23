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

static inline bool mid_entry_uses_heap(const MidEntry *e) {
    return e->rule_count > MID_ENTRY_INLINE_CAP + 1;
}

static inline int32_t mid_entry_rest_id(const MidEntry *e, uint32_t k) {
    if (mid_entry_uses_heap(e)) {
        return e->rest.rule_ids_rest[k];
    }
    return e->rest.inline_ids[k];
}

static void free_mid_entry_contents(MidEntry *entry) {
    if (entry == NULL)
        return;
    if (mid_entry_uses_heap(entry) && entry->rest.rule_ids_rest != NULL) {
        free(entry->rest.rule_ids_rest);
    }
    entry->rest.rule_ids_rest = NULL;
}

static inline size_t get_middle_cap(const MidEntry *middle) {
    if (middle == NULL)
        return 0;
    return ((const size_t *)middle)[-1];
}

static inline MidEntry *alloc_middle(size_t cap) {
    size_t *raw = malloc(sizeof(size_t) + cap * sizeof(MidEntry));
    if (!raw)
        return NULL;
    raw[0] = cap;
    return (MidEntry *)(raw + 1);
}

static inline MidEntry *realloc_middle(MidEntry *middle, size_t new_cap) {
    if (middle == NULL)
        return alloc_middle(new_cap);
    size_t *raw = (size_t *)middle - 1;
    size_t *new_raw = realloc(raw, sizeof(size_t) + new_cap * sizeof(MidEntry));
    if (!new_raw)
        return NULL;
    new_raw[0] = new_cap;
    return (MidEntry *)(new_raw + 1);
}

static inline void free_middle(MidEntry *middle) {
    if (middle == NULL)
        return;
    size_t *raw = (size_t *)middle - 1;
    free(raw);
}

static void free_all_paths_elem_internal(AllPathsElem *elem) {
    if (elem == NULL || elem->n == 0)
        return;

    if (elem->n == 1) {
        free_mid_entry_contents(&elem->data.single_elem);
    } else if (elem->data.middle != NULL) {
        for (size_t i = 0; i < elem->n; i++) {
            free_mid_entry_contents(&elem->data.middle[i]);
        }
        free_middle(elem->data.middle);
        elem->data.middle = NULL;
    }
    elem->n = 0;
}

static void mid_entry_add_rule(MidEntry *e, int32_t rule_id) {
    if (e->rule_count == 0) {
        e->rule_id0 = rule_id;
        e->rule_count = 1;
        return;
    }

    if (e->rule_id0 == rule_id)
        return;

    uint32_t extra = e->rule_count - 1;

    if (!mid_entry_uses_heap(e)) {
        for (uint32_t k = 0; k < extra; k++) {
            if (e->rest.inline_ids[k] == rule_id) {
                return;
            }
        }

        if (extra < MID_ENTRY_INLINE_CAP) {
            e->rest.inline_ids[extra] = rule_id;
            e->rule_count++;
            return;
        }

        int32_t *heap = malloc((extra + 1) * sizeof(int32_t));
        memcpy(heap, e->rest.inline_ids, extra * sizeof(int32_t));
        heap[extra] = rule_id;
        e->rest.rule_ids_rest = heap;
        e->rule_count++;
        return;
    }

    for (uint32_t k = 0; k < extra; k++) {
        if (e->rest.rule_ids_rest[k] == rule_id) {
            return;
        }
    }

    int32_t *tmp = realloc(e->rest.rule_ids_rest, (extra + 1) * sizeof(int32_t));
    tmp[extra] = rule_id;
    e->rest.rule_ids_rest = tmp;
    e->rule_count++;
}

static void mid_entry_merge_rules(MidEntry *dst, const MidEntry *src) {
    if (src->rule_count == 0)
        return;

    mid_entry_add_rule(dst, src->rule_id0);
    for (uint32_t k = 0; k + 1 < src->rule_count; k++) {
        mid_entry_add_rule(dst, mid_entry_rest_id(src, k));
    }
}

static inline size_t all_paths_next_cap(size_t cur_cap, size_t need) {
    size_t cap = (cur_cap == 0) ? 4 : cur_cap;
    while (cap < need) {
        cap *= 2;
    }
    return cap;
}

static void insert_all_paths(AllPathsElem *elem, MidEntry *value) {
    MidEntry *arr = elem->data.middle;
    size_t len = elem->n;

    size_t l = 0, r = len;
    while (l < r) {
        size_t m = l + (r - l) / 2;
        if (arr[m].mid < value->mid)
            l = m + 1;
        else
            r = m;
    }

    if (l < len && arr[l].mid == value->mid) {
        mid_entry_merge_rules(&arr[l], value);
        free_mid_entry_contents(value);
        return;
    }

    size_t cur_cap = get_middle_cap(arr);
    if (len == cur_cap) {
        size_t new_cap = all_paths_next_cap(cur_cap, len + 1);
        arr = realloc_middle(arr, new_cap);
        elem->data.middle = arr;
    }

    if (l < len) {
        memmove(&arr[l + 1], &arr[l], (len - l) * sizeof(MidEntry));
    }
    arr[l] = *value;
    elem->n = len + 1;
}

static MidEntry *merge_all_paths(size_t *out_n, MidEntry *a, size_t na, MidEntry *b,
                                      size_t nb) {
    size_t alloc_cap = na + nb;
    MidEntry *tmp = alloc_middle(alloc_cap);
    size_t ia = 0, ib = 0, outn = 0;

    while (ia < na && ib < nb) {
        if (a[ia].mid < b[ib].mid) {
            tmp[outn++] = a[ia++];
        } else if (b[ib].mid < a[ia].mid) {
            tmp[outn++] = b[ib++];
        } else {
            mid_entry_merge_rules(&a[ia], &b[ib]);
            free_mid_entry_contents(&b[ib]);
            tmp[outn++] = a[ia];
            ia++;
            ib++;
        }
    }
    while (ia < na) {
        tmp[outn++] = a[ia++];
    }
    while (ib < nb) {
        tmp[outn++] = b[ib++];
    }

    *out_n = outn;

    return tmp;
}

static void add_all_paths(AllPathsElem *z, AllPathsElem *x, AllPathsElem *y) {
    if (x->n == 0) {
        *z = *y;
        return;
    }
    if (y->n == 0) {
        *z = *x;
        return;
    }

    if (x->n == 1 && y->n == 1) {
        MidEntry xs = x->data.single_elem;
        MidEntry ys = y->data.single_elem;
        if (xs.mid == ys.mid) {
            mid_entry_merge_rules(&xs, &ys);
            free_mid_entry_contents(&ys);
            z->n = 1;
            z->data.single_elem = xs;
        } else {
            MidEntry lo = (xs.mid < ys.mid) ? xs : ys;
            MidEntry hi = (xs.mid < ys.mid) ? ys : xs;
            size_t cap = 4;
            MidEntry *arr = alloc_middle(cap);
            arr[0] = lo;
            arr[1] = hi;
            z->n = 2;
            z->data.middle = arr;
        }
        return;
    }

    if (x->n == 1 || y->n == 1) {
        AllPathsElem *big = (x->n == 1) ? y : x;
        MidEntry val = (x->n == 1) ? x->data.single_elem : y->data.single_elem;
        insert_all_paths(big, &val);
        *z = *big;
        return;
    }

    MidEntry *a = x->data.middle, *b = y->data.middle;
    size_t na = x->n, nb = y->n;
    size_t zn;
    MidEntry *merged = merge_all_paths(&zn, a, na, b, nb);
    free_middle(a);
    free_middle(b);
    z->n = zn;
    z->data.middle = merged;
}

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

static inline GrB_Info rule_table_push(BinaryRuleInfo **table, size_t *count, size_t *cap,
                                       int32_t nonterm, int32_t B, int32_t C) {
    if (*count == *cap) {
        size_t new_cap = (*cap == 0) ? 64 : (*cap * 2);
        BinaryRuleInfo *tmp = realloc(*table, new_cap * sizeof(BinaryRuleInfo));
        if (!tmp)
            return GrB_OUT_OF_MEMORY;
        *table = tmp;
        *cap = new_cap;
    }
    (*table)[*count] = (BinaryRuleInfo){.nonterm = nonterm, .B = B, .C = C};
    (*count)++;
    return GrB_SUCCESS;
}

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
