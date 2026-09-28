#ifndef LG_CFL_ALLPATHS_INTERNAL_H
#define LG_CFL_ALLPATHS_INTERNAL_H

#include "LG_internal.h"
#include <LAGraphX.h>

// Checks whether the MidEntry structure uses heap memory to store additional rule IDs
static inline bool mid_entry_uses_heap(const MidEntry *e) {
    return e->rule_count > MID_ENTRY_INLINE_CAP + 1;
}

// Retrieves the k-th additional rule ID from either inline array or heap allocation
static inline int32_t mid_entry_rest_id(const MidEntry *e, uint32_t k) {
    if (mid_entry_uses_heap(e)) {
        return e->rest.rule_ids_rest[k];
    }
    return e->rest.inline_ids[k];
}

// Frees heap-allocated rule ID array inside a MidEntry structure if allocated
static inline void free_mid_entry_contents(MidEntry *entry) {
    if (entry == NULL)
        return;
    if (mid_entry_uses_heap(entry) && entry->rest.rule_ids_rest != NULL) {
        free(entry->rest.rule_ids_rest);
    }
    entry->rest.rule_ids_rest = NULL;
}

// Adds a rule ID to MidEntry, avoiding duplicates and transitioning to heap allocation
// when inline capacity is exceeded
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
            if (e->rest.inline_ids[k] == rule_id)
                return;
        }

        if (extra < MID_ENTRY_INLINE_CAP) {
            e->rest.inline_ids[extra] = rule_id;
            e->rule_count++;
            return;
        }

        // Allocate heap memory when inline capacity is exceeded
        int32_t *heap = malloc((extra + 1) * sizeof(int32_t));
        memcpy(heap, e->rest.inline_ids, extra * sizeof(int32_t));
        heap[extra] = rule_id;
        e->rest.rule_ids_rest = heap;
        e->rule_count++;
        return;
    }

    for (uint32_t k = 0; k < extra; k++) {
        if (e->rest.rule_ids_rest[k] == rule_id)
            return;
    }

    int32_t *tmp = realloc(e->rest.rule_ids_rest, (extra + 1) * sizeof(int32_t));
    tmp[extra] = rule_id;
    e->rest.rule_ids_rest = tmp;
    e->rule_count++;
}

// Merges all rule IDs from src MidEntry into dst MidEntry
static void mid_entry_merge_rules(MidEntry *dst, const MidEntry *src) {
    if (src->rule_count == 0)
        return;

    mid_entry_add_rule(dst, src->rule_id0);
    for (uint32_t k = 0; k + 1 < src->rule_count; k++) {
        mid_entry_add_rule(dst, mid_entry_rest_id(src, k));
    }
}

// Retrieves allocated capacity stored in hidden header prefix before middle array
static inline size_t get_middle_cap(const MidEntry *middle) {
    if (middle == NULL)
        return 0;
    return ((const size_t *)middle)[-1];
}

// Allocates array of MidEntry elements with a capacity header prefix
static inline MidEntry *alloc_middle(size_t cap) {
    size_t *raw = malloc(sizeof(size_t) + cap * sizeof(MidEntry));
    if (!raw)
        return NULL;
    raw[0] = cap;
    return (MidEntry *)(raw + 1);
}

// Reallocates array of MidEntry elements preserving the capacity header prefix
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

// Frees array of MidEntry elements including its capacity header prefix
static inline void free_middle(MidEntry *middle) {
    if (middle == NULL)
        return;
    size_t *raw = (size_t *)middle - 1;
    free(raw);
}

// Calculates next capacity growth step for AllPathsElem middle array
static inline size_t all_paths_next_cap(size_t cur_cap, size_t need) {
    size_t cap = (cur_cap == 0) ? 4 : cur_cap;
    while (cap < need) {
        cap += cap / 2 + 1;
    }
    return cap;
}

// Helper function to free internal dynamic memory allocated inside AllPathsElem
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

// Inserts or merges a MidEntry into the ordered middle array of AllPathsElem
static void insert_all_paths(AllPathsElem *elem, MidEntry *value) {
    MidEntry *arr = elem->data.middle;
    size_t len = elem->n;

    // Array is ordered, so we can use binary search to find the position to insert value
    size_t l = 0, r = len;
    while (l < r) {
        size_t m = l + (r - l) / 2;
        if (arr[m].mid < value->mid)
            l = m + 1;
        else
            r = m;
    }

    // If mid vertex is already in the array, merge rules and free value's dynamic resources
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

// Merging two ordered arrays of MidEntry intermediate vertices in the add function
static MidEntry *merge_all_paths(size_t *out_n, MidEntry *a, size_t na,
                                        MidEntry *b, size_t nb) {
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
    while (ia < na)
        tmp[outn++] = a[ia++];
    while (ib < nb)
        tmp[outn++] = b[ib++];

    *out_n = outn;
    return tmp;
}

// Combines two AllPathsElem elements during addition in the monoid
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
            // Pre-size the array a bit above the 2 entries actually used, so
            // that a subsequent insert_all_paths() does not need to grow it
            // immediately.
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

// Appends binary rule info (nonterm -> B C) to the dynamic rule table array
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

#endif // LG_CFL_ALLPATHS_INTERNAL_H
