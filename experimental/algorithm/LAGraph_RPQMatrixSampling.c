// GraphBLAS helpers for the RPQ static and sampling cardinality estimators.
#include "LG_internal.h"
#include "LAGraphX.h"

#define RPQ_OK(method) do { GrB_Info info = (method); if (info != GrB_SUCCESS) return info; } while (0)
static char *msg = NULL;

GrB_Info LAGraph_RPQMatrix_sample_seed (
    GrB_Matrix *seed, const GrB_Index *sources, GrB_Index nsources, GrB_Index n)
{
    LG_ASSERT(seed != NULL, GrB_NULL_POINTER);
    LG_ASSERT(sources != NULL || nsources == 0, GrB_NULL_POINTER);
    RPQ_OK(GrB_Matrix_new(seed, GrB_BOOL, nsources, n));
    for (GrB_Index row = 0; row < nsources; row++)
    {
        if (sources[row] >= n)
        {
            RPQ_OK(GrB_Matrix_free(seed));
            return GrB_INVALID_INDEX;
        }
        RPQ_OK(GrB_Matrix_setElement_BOOL(*seed, true, row, sources[row]));
    }
    return GrB_SUCCESS;
}

GrB_Info LAGraph_RPQMatrix_sample_apply (
    GrB_Matrix *result, GrB_Matrix seed, GrB_Matrix relation,
    bool transpose_relation)
{
    LG_ASSERT(result != NULL, GrB_NULL_POINTER);
    LG_ASSERT(seed != GrB_NULL && relation != GrB_NULL, GrB_NULL_POINTER);
    GrB_Index sr, sc, rr, rc;
    RPQ_OK(GrB_Matrix_nrows(&sr, seed));
    RPQ_OK(GrB_Matrix_ncols(&sc, seed));
    RPQ_OK(GrB_Matrix_nrows(&rr, relation));
    RPQ_OK(GrB_Matrix_ncols(&rc, relation));
    if (sc != (transpose_relation ? rc : rr)) return GrB_DIMENSION_MISMATCH;
    RPQ_OK(GrB_Matrix_new(result, GrB_BOOL, sr,
        transpose_relation ? rr : rc));
    GrB_Info info = GrB_mxm(*result, GrB_NULL, GrB_NULL, GxB_ANY_PAIR_BOOL,
        seed, relation, transpose_relation ? GrB_DESC_T1 : GrB_NULL);
    if (info != GrB_SUCCESS) GrB_Matrix_free(result);
    return info;
}

GrB_Info LAGraph_RPQMatrix_sample_union (
    GrB_Matrix *result, GrB_Matrix lhs, GrB_Matrix rhs)
{
    LG_ASSERT(result != NULL, GrB_NULL_POINTER);
    LG_ASSERT(lhs != GrB_NULL && rhs != GrB_NULL, GrB_NULL_POINTER);
    GrB_Index lr, lc, rr, rc;
    RPQ_OK(GrB_Matrix_nrows(&lr, lhs)); RPQ_OK(GrB_Matrix_ncols(&lc, lhs));
    RPQ_OK(GrB_Matrix_nrows(&rr, rhs)); RPQ_OK(GrB_Matrix_ncols(&rc, rhs));
    if (lr != rr || lc != rc) return GrB_DIMENSION_MISMATCH;
    RPQ_OK(GrB_Matrix_new(result, GrB_BOOL, lr, lc));
    GrB_Info info = GrB_eWiseAdd(*result, GrB_NULL, GrB_NULL,
        GxB_ANY_BOOL, lhs, rhs, GrB_NULL);
    if (info != GrB_SUCCESS) GrB_Matrix_free(result);
    return info;
}

GrB_Info LAGraph_RPQMatrix_sample_dup (GrB_Matrix *result, GrB_Matrix source)
{
    LG_ASSERT(result != NULL, GrB_NULL_POINTER);
    LG_ASSERT(source != GrB_NULL, GrB_NULL_POINTER);
    return GrB_Matrix_dup(result, source);
}

GrB_Info LAGraph_RPQMatrix_sample_stats (
    GrB_Index *nvals, GrB_Index *active_rows, GrB_Index *active_cols,
    GrB_Matrix sample)
{
    LG_ASSERT(nvals && active_rows && active_cols, GrB_NULL_POINTER);
    LG_ASSERT(sample != GrB_NULL, GrB_NULL_POINTER);
    RPQ_OK(GrB_Matrix_nvals(nvals, sample));
    RPQ_OK(LAGraph_RPQMatrix_reduce(active_rows, sample, 0));
    RPQ_OK(LAGraph_RPQMatrix_reduce(active_cols, sample, 1));
    return GrB_SUCCESS;
}

GrB_Info LAGraph_RPQMatrix_reduce_count_vector (
    GrB_Vector *res, GrB_Matrix mat, uint8_t reduce_type)
{
    LG_ASSERT(res != NULL && mat != GrB_NULL, GrB_NULL_POINTER);
    GrB_Index rows, cols;
    RPQ_OK(GrB_Matrix_nrows(&rows, mat)); RPQ_OK(GrB_Matrix_ncols(&cols, mat));
    if (reduce_type > 1) return GrB_INVALID_VALUE;
    RPQ_OK(GrB_Vector_new(res, GrB_UINT64, reduce_type == 0 ? rows : cols));
    GrB_Info info = GrB_reduce(*res, GrB_NULL, GrB_NULL,
        GrB_PLUS_MONOID_UINT64, mat, reduce_type == 0 ? GrB_NULL : GrB_DESC_T0);
    if (info != GrB_SUCCESS) GrB_Vector_free(res);
    return info;
}

GrB_Info LAGraph_RPQMatrix_count_vector_dot (
    double *res, GrB_Vector lhs, GrB_Vector rhs)
{
    LG_ASSERT(res != NULL, GrB_NULL_POINTER);
    GrB_Index ls, rs; RPQ_OK(GrB_Vector_size(&ls, lhs)); RPQ_OK(GrB_Vector_size(&rs, rhs));
    if (ls != rs) return GrB_DIMENSION_MISMATCH;
    GrB_Vector product = GrB_NULL;
    RPQ_OK(GrB_Vector_new(&product, GrB_FP64, ls));
    GrB_Info info = GrB_eWiseMult(product, GrB_NULL, GrB_NULL,
        GrB_TIMES_FP64, lhs, rhs, GrB_NULL);
    if (info == GrB_SUCCESS)
        info = GrB_reduce(res, GrB_NULL, GrB_PLUS_MONOID_FP64, product, GrB_NULL);
    GrB_Vector_free(&product);
    return info;
}

GrB_Info LAGraph_RPQMatrix_count_vector_sum (double *res, GrB_Vector vector)
{
    LG_ASSERT(res != NULL && vector != GrB_NULL, GrB_NULL_POINTER);
    return GrB_reduce(res, GrB_NULL, GrB_PLUS_MONOID_FP64, vector, GrB_NULL);
}

GrB_Info LAGraph_RPQMatrix_count_vector_nvals (GrB_Index *res, GrB_Vector vector)
{
    LG_ASSERT(res != NULL && vector != GrB_NULL, GrB_NULL_POINTER);
    return GrB_Vector_nvals(res, vector);
}

GrB_Info LAGraph_RPQMatrix_count_vector_scale (
    GrB_Vector *res, GrB_Vector vector, double scale, double cap)
{
    LG_ASSERT(res != NULL && vector != GrB_NULL, GrB_NULL_POINTER);
    GrB_Index size; RPQ_OK(GrB_Vector_size(&size, vector));
    RPQ_OK(GrB_Vector_new(res, GrB_FP64, size));
    GrB_Info info = GrB_apply(*res, GrB_NULL, GrB_NULL,
        GrB_TIMES_FP64, scale, vector, GrB_NULL);
    if (info == GrB_SUCCESS)
        info = GrB_apply(*res, GrB_NULL, GrB_NULL, GrB_MIN_FP64, cap, *res, GrB_NULL);
    if (info != GrB_SUCCESS) GrB_Vector_free(res);
    return info;
}

GrB_Info LAGraph_RPQMatrix_count_vector_add (
    GrB_Vector *res, GrB_Vector lhs, GrB_Vector rhs, double cap)
{
    LG_ASSERT(res != NULL, GrB_NULL_POINTER);
    GrB_Index ls, rs; RPQ_OK(GrB_Vector_size(&ls, lhs)); RPQ_OK(GrB_Vector_size(&rs, rhs));
    if (ls != rs) return GrB_DIMENSION_MISMATCH;
    RPQ_OK(GrB_Vector_new(res, GrB_FP64, ls));
    GrB_Info info = GrB_eWiseAdd(*res, GrB_NULL, GrB_NULL,
        GrB_PLUS_FP64, lhs, rhs, GrB_NULL);
    if (info == GrB_SUCCESS)
        info = GrB_apply(*res, GrB_NULL, GrB_NULL, GrB_MIN_FP64, cap, *res, GrB_NULL);
    if (info != GrB_SUCCESS) GrB_Vector_free(res);
    return info;
}

GrB_Info LAGraph_RPQMatrix_count_vector_free (GrB_Vector *vector)
{
    LG_ASSERT(vector != NULL, GrB_NULL_POINTER);
    return GrB_Vector_free(vector);
}
