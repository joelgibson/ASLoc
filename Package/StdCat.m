// A StdMor encodes a morphism in the additive envelope of the W-groupoid category
// enriched over the ring Q. The domain and codomain are sequences of elements from
// the group W, which each encode a formal direct sum. The morphism itself is encoded
// as a matrix with entries in Q, rows corresponding to the domain and columns to the
// codomain. The matrix must only be supported over (row, column) pairs such that
// domain[row] = codomain[column].
declare type StdMor;
declare attributes StdMor:
    dom, // A SeqEnum[GrpFPCoxElt] giving the domain of the morphism.
    cod, // A SeqEnum[GrpFPCoxElt] giving the codomain of the morphism.
    mat, // A sparse matrix with #dom rows and #cod columns.
    deg; // An integer giving the degree of the morphism.


// Internal constructor for StdMor.
// Package-internal functions can use this to sidestep the more stringent checks in the user-facing constructors.
// - Assert level 1: checks that the number of elements in the domain and codomain match the shape of the matrix.
// - Assert level 2: checks that the matrix is supported only where the domain element matches the codomain element.
function StdMorConstruct(dom, cod, mat, deg)
    assert #dom eq Nrows(mat);
    assert #cod eq Ncols(mat);
    assert2 forall{pair : pair in Support(mat) | dom[pair[1]] eq cod[pair[2]]};

    f := New(StdMor);
    f`dom := dom;
    f`cod := cod;
    f`mat := mat;
    f`deg := deg;
    return f;
end function;

intrinsic StdMorphism(dom::SeqEnum[GrpFPCoxElt], cod::SeqEnum[GrpFPCoxElt], mat::MtrxSprs : deg := 0) -> StdMor
{Create a morphism in the standard category, with given domain and codomain. The coefficient ring
is determined by the matrix. This constructor always checks that the matrix dimensions are compatible
with the domain and codomain, and that the matrix is only supported at points where the domain element
is equal to the codomain element.}
    require #dom eq Nrows(mat): "Domain had", #dom, "elements but matrix had", Nrows(mat), "rows";
    require #cod eq Ncols(mat): "Codomain had", #cod, "elements but matrix had", Ncols(mat), "columns";
    require
        forall{pair : pair in Support(mat) | dom[pair[1]] eq cod[pair[2]]}:
        "Nonzero entry at some entry (x, y) where x is not equal to y.";

    return StdMorConstruct(dom, cod, mat, deg);
end intrinsic;

intrinsic StdMorphism(ring::Rng, obj::SeqEnum[GrpFPCoxElt]) -> StdMor
{The identity morphism on the given object, with coefficients in the given ring.}
    return StdMorConstruct(obj, obj, IdentitySparseMatrix(ring, #obj), 0);
end intrinsic;

intrinsic StdMorphism(ring::Rng, dom::SeqEnum[GrpFPCoxElt], cod::SeqEnum[GrpFPCoxElt], rows::SeqEnum[SeqEnum[RngElt]] : deg := 0) -> StdMor
{A morphism given by rows in a matrix over the ring. This constructor is intended to be used for literals.}
    return StdMorphism(dom, cod, SparseMatrix(Matrix(ring, rows)) : deg := deg);
end intrinsic;

intrinsic IsOne(f::StdMor) -> BoolElt
{A predicate returning true if f is the identity map on an object.}
    return (f`dom eq f`cod) and IsOne(f`mat);
end intrinsic;

intrinsic IsScalar(f::StdMor) -> BoolElt, RngElt
{A predicate returning true if f is a scalar map on an object. If true, the scalar is also returned.
If false, 0 is returned.}

    // To be considered a scalar, domain and codomain must be equal, and degree must be zero.
    if f`dom ne f`cod or f`deg ne 0 then
        return false;
    end if;

    if IsScalar(f`mat) then
        return true, (Nrows(f`mat) ne 0) select f`mat[1, 1] else 1;
    end if;

    return false, 0;
end intrinsic;

intrinsic IsZero(f::StdMor) -> BoolElt
{Is this the zero morphism?}
    return IsZero(f`mat);
end intrinsic;

intrinsic Print(f::StdMor)
{Print}
    printf "StdMor from a %o element sequence to a %o element sequence of degree %o over %o",
        #f`dom, #f`cod, f`deg, CoefficientRing(f`mat);
end intrinsic;

intrinsic Domain(f::StdMor) -> SeqEnum[GrpFPCoxElt]
{The domain of the morphism, a sequence of Coxeter group elements.}
    return f`dom;
end intrinsic;

intrinsic Codomain(f::StdMor) -> SeqEnum[GrpFPCoxElt]
{The codomain of the morphism, a sequence of Coxeter group elements.}
    return f`cod;
end intrinsic;

intrinsic CoefficientRing(f::StdMor) -> Rng
{The ring the morphism is defined over.}
    return CoefficientRing(f`mat);
end intrinsic;

intrinsic Matrix(f::StdMor) -> Mtrx
{Return the dense matrix underlying f. For interactive or debugging use.}
    return Matrix(f`mat);
end intrinsic;

intrinsic 'eq'(f::StdMor, g::StdMor) -> BoolElt
{Check equality of morphisms.}
    return (f`deg eq g`deg) and (f`mat eq g`mat) and (f`cod eq g`cod) and (f`dom eq g`dom);
end intrinsic;

intrinsic '*'(q::RngElt, f::StdMor) -> StdMor
{Scale the morphism by an element coercible into the coefficient ring.}
    return StdMorphism(f`dom, f`cod, q * f`mat : deg := f`deg);
end intrinsic;

intrinsic '+'(f::StdMor, g::StdMor) -> StdMor
{Add two morphisms, checking domain, codomain, and degree.}
    require #f`dom eq #g`dom: "Domain mismatch: left domain is size", #f`dom, "right is", #g`dom;
    require #f`cod eq #g`cod: "Codomain mismatch: left codomain is size", #f`dom, "right is", #g`dom;
    require f`dom eq g`dom: "Domain mismatch: left and right domains are the same size, but are different sequences.";
    require f`cod eq g`cod: "Codomain mismatch: left and right domains are the same size, but are different sequences.";
    require f`deg eq g`deg: "Degree mismatch: left degree is", f`deg, "right degree is", g`deg;

    return StdMorConstruct(f`dom, f`cod, f`mat + g`mat, f`deg);
end intrinsic;

intrinsic '-'(f::StdMor, g::StdMor) -> StdMor
{Subtract two morphisms, checking domain, codomain, and degree.}
    require #f`dom eq #g`dom: "Domain mismatch: left domain is size", #f`dom, "right is", #g`dom;
    require #f`cod eq #g`cod: "Codomain mismatch: left codomain is size", #f`dom, "right is", #g`dom;
    require f`dom eq g`dom: "Domain mismatch: left and right domains are the same size, but are different sequences.";
    require f`cod eq g`cod: "Codomain mismatch: left and right domains are the same size, but are different sequences.";
    require f`deg eq g`deg: "Degree mismatch: left degree is", f`deg, "right degree is", g`deg;

    return StdMorConstruct(f`dom, f`cod, f`mat - g`mat, f`deg);
end intrinsic;

intrinsic '*'(f::StdMor, g::StdMor) -> StdMor
{Return the composition (f o g), corresponding to the vertical stacking of f on top of g.
This function always checks compatibility between the codomain of g and the domain of f.}
    require #g`cod eq #f`dom:
        "Domain and codomain mismatch: left domain has",
        #f`dom,
        "elements, right codomain has",
        #g`cod;
    require g`cod eq f`dom:
        "Domain and codomain mismatch: dimensions agree but standard sequences do not.",
        "\nLeft domain:   ", f`dom, "Right codomain:", g`cod;

    // We should be right to use the internal constructor directly. If both f and g satisfy
    // the property that they are nonzero only where their domains and codomains match, then
    // f * g should satisfy this as well.
    return StdMorConstruct(g`dom, f`cod, g`mat * f`mat, f`deg + g`deg);
end intrinsic;

intrinsic Transpose(f::StdMor) -> StdMor
{Return the transpose of f, in its matrix basis.}
    return StdMorConstruct(f`cod, f`dom, Transpose(f`mat), f`deg);
end intrinsic;

intrinsic Inverse(f::StdMor) -> StdMor
{Return the inverse of f.}
    require #f`dom eq #f`cod: "Cannot invert a map different cardinality domain and codomain.";
    return StdMorphism(f`cod, f`dom, SparseInverse(f`mat) : deg := -f`deg);
end intrinsic;

intrinsic '-'(f::StdMor) -> StdMor
{Return the negative of f.}
    return StdMorConstruct(f`cod, f`dom, -f`mat, f`deg);
end intrinsic;

intrinsic Tensor(seq1::SeqEnum[GrpFPCoxElt], seq2::SeqEnum[GrpFPCoxElt]) -> SeqEnum[GrpFPCoxElt]
{Return the tensor product of objects in the standard category. By convention, indices on the right
change faster than indices on the left, so (a + b + c)(x + y) = (ax + ay + bx + by + cx + cy).}
    return [x * y : y in seq2, x in seq1];
end intrinsic;

intrinsic Tensor(act, f::StdMor, g::StdMor) -> StdMor
{Given morphisms f and g with coefficient ring Q, and an action act : W x Q -> Q, return the
tensor product of morphisms.}
    newDom := Tensor(f`dom, g`dom);
    newCod := Tensor(f`cod, g`cod);
    newMat := SparseMatrix(CoefficientRing(f`mat), #newDom, #newCod);

    // This is essentially a sparse Kronecker product, with the elements on the right
    // twisted depending on the Weyl group element on the left.
    for left in Eltseq(f`mat) do
        // It is faster to do (a * M) for a sparse matrix than to do (M *:= a), as of Magma V2.26-6.
        InsertBlock(
            ~newMat,
            left[3] * ChangeRing(g`mat, act(f`dom[left[1]])),
            (left[1] - 1) * #g`dom + 1,
            (left[2] - 1) * #g`cod + 1
        );
    end for;

    return StdMorConstruct(newDom, newCod, newMat, f`deg + g`deg);
end intrinsic;

intrinsic Tensor(act, f::StdMor, obj::SeqEnum[GrpFPCoxElt]) -> StdMor
{Return the tensor product of f with the identity morphism of obj.}
    return Tensor(act, f, StdMorphism(CoefficientRing(f`mat), obj));
end intrinsic;

intrinsic Tensor(act, obj::SeqEnum[GrpFPCoxElt], g::StdMor) -> StdMor
{Return the tensor product of the identity morphism of obj with g.}
    return Tensor(act, StdMorphism(CoefficientRing(g`mat), obj), g);
end intrinsic;

intrinsic DecomposeIdem(f::StdMor) -> StdMor, StdMor
{Return two StdMors p, i where i * p = f and p * i = identity, or error if no solution exists.}
    require f`deg eq 0: "f is not in degree zero, so cannot be decomposed as an idempotent.";

    // Return a solution to proj * incl = f`mat.
    proj, incl := SparseDecompose(f`mat);

    // Verify idempotency: if M = PI and IP = 1, then M^2 = PIPI = PI = M. This should be faster
    // than actually just multiplying M with itself in some cases! (Not sure why, perhaps sparse
    // matrix multiplication is not that quick?).
    error if not IsOne(incl * proj), "Matrix was not idempotent.";

    // The columns of incl still correspond to the standard object, but the rows returned
    // are just some basis for the row-space of M. We need to write down a standard sequence
    // representing the domain of incl, or codomain of proj. There should only be one
    // possibility, since whenever a nonzero entry occurs the column and row objects should
    // agree, and since we have a basis every row has at least one entry.
    factor := [];
    for i in [1..Nrows(incl)] do
        for j in [1..Ncols(incl)] do
            if incl[i, j] ne 0 then
                Append(~factor, f`cod[j]);
                break;
            end if;
        end for;
    end for;

    assert #factor eq Nrows(incl);

    inclMor := StdMorphism(factor, f`dom, SparseMatrix(incl));
    projMor := StdMorphism(f`dom, factor, SparseMatrix(proj));

    return projMor, inclMor;
end intrinsic;

// TODO: Replace LimitDomain and LimitCodomain once Magma gets a fast sparse Submatrix function.

intrinsic LimitDomain(f::StdMor, i::RngIntElt) -> StdMor
{Return the 1-row submatrix of f consisting of the ith row.}
    require 1 le i and i le #f`dom:
        "Cannot take row submatrix", i, "of a matrix with", #f`dom, "rows";
    return StdMorConstruct([f`dom[i]], f`cod, RowSubmatrixRange(f`mat, i, i), f`deg);
end intrinsic;

intrinsic LimitCodomain(f::StdMor, j::RngIntElt) -> StdMor
{Return the 1-column submatrix of f consisting of the jth column.}
    require 1 le j and j le #f`cod:
        "Cannot take column submatrix", j, "of a matrix with", #f`cod, "columns";
    return StdMorConstruct(f`dom, [f`cod[j]], ColumnSubmatrixRange(f`mat, j, j), f`deg);
end intrinsic;
