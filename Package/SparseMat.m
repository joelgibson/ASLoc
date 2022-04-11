// Intrinsics giving fast operations on sparse matrices, using the internal Echelonize function.

intrinsic SparseDecompose(M::MtrxSprs) -> MtrxSprs, MtrxSprs
{Return (proj, incl) such that M = proj * incl, with incl an isomorphism onto its image.
This function sets proj to the RREF of M with zero rows removed.}

    // Set incl to the non-zero rows of the reduced row-echelon form of M.
    incl := M;
    Echelonize(~incl);

    // Now we want to solve the equation M = proj * incl. The fastest tool we have is
    // Echelonize, which does things along rows rather than columns, so transpose the
    // equation to read incl^T * proj^T = M^T. To solve this kind of linear system, we
    // form the augmented matrix (incl^T | M^T) and row-reduce. Since incl has full rank,
    // after reducing we will end up with a block matrix
    // ( I | proj^T )
    // ( 0 | X )
    // and X should be zero if there is indeed a solution to the equation.
    aug := Transpose(VerticalJoin(incl, M));
    Echelonize(~aug);
    bottom := RowSubmatrixRange(aug, Nrows(incl) + 1, Nrows(aug));
    error if not IsZero(bottom),
        "There was no solution to the system (M was not an idempotent).";
    proj := Transpose(Submatrix(aug, 1, Nrows(incl) + 1, Nrows(incl), Ncols(incl)));

    assert proj * incl eq M;

    return proj, incl;
end intrinsic;

intrinsic SparseInverse(M::MtrxSprs) -> MtrxSprs
{Return the inverse of M, or error if it is not invertible.}
    require Nrows(M) eq Ncols(M): "Matrix was not square: had dimensions", Nrows(M), "x", Ncols(M);

    aug := HorizontalJoin(M, IdentitySparseMatrix(CoefficientRing(M), Nrows(M)));
    Echelonize(~aug);
    require IsOne(ColumnSubmatrix(aug, 1, Nrows(M))):
        "The matrix was not invertible: had rank", Rank(M), "rather than", Nrows(M);

    return ColumnSubmatrix(aug, Nrows(M) + 1, Nrows(M));
end intrinsic;
