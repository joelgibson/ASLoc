declare verbose ASLoc, 3;

import "StdCat.m": StdMorConstruct;

// TODO: We could clean up a lot of the actions here. Currently there are many cases for when
//       we want to interpret a sequence of integers as a Bott-Samelson identity morphism or as
//       a Bott-Samelson object for instance. We should probably have some way of converting a
//       sequence so that we actually consider it as an object, and then just define things on
//       that object.

declare type BSCat[BSMor];
declare attributes BSCat:
    // The diagrammatic category is defined for a Cartan matrix C, a Coxeter group W, and
    // a polynomial ring R with a map Act[s]: R -> R for each simple generator s. We do
    // not use the polynomial ring R directly, rather we only use its field of fractions
    // FR (see below).
    C, W,

    // In order to represent the images of morphisms in the standard category (with no
    // parabolic quotient yet), we use the field of fractions FR of R, and the induced
    // action map FAct on this field. The field FQ and the action FAct are what appears
    // in the paper "Localized calculus for the Hecke category": the field Q in the paper
    // goes by the name FR here.
    FR, FAct,

    // Finally, we consider a (possibly trivial) parabolic quotient by some parabolic
    // subgroup of W, defined by a subset I of the simple generators. There should be
    // a map of rings Spec: FR -> Q (which need not be defined on the whole of FR) giving
    // the specialisation into Q: on the simple generators the map Spec should kill those
    // belonging to I, with those in the complement remaining invertible.
    //
    // If no parabolic quotient is desired, one could take I = {}, Q = FR, and the
    // specialisation map Spec: FR -> FR the identity.
    //
    // TODO: Explain QBase more. It is the ring that the intersection form is valued in.
    I, Q, Spec, QBase,

    // In order to speed up certain functions we use some caches. These caches are just implementation
    // details, and should never be accessed outside this file.
    StdProdSimpleCache, FActionByEltCache, FSpecActionByEltCache, BSActIdCache, BraidCache,

    // Misc associative array for occasional development use, eg collecting statistics and so on.
    meta;


// A BSMor encodes the domain and codomain of a morphism in the Bott-Samelson category,
// along with its image under the localisation functor in the standard category. Computing
// with these morphisms is quite slow: they are intended to be used as generators to act on
// the localised category. The only coefficient ring appearing in BSMor should be FR, not Q.
declare type BSMor;
declare attributes BSMor:
    Parent, // A BSCat.
    bsdom,  // A SeqEnum[RngIntElt] giving the domain of the morphism.
    bscod,  // A SeqEnum[RngIntElt] giving the codomain of the morphism.
    stdmor; // A StdMor giving the un-untruncated morphism.


intrinsic BSCategory(C::AlgMatElt, W::GrpFPCox) -> BSCat
{The localised diagrammatic category with no parabolic quotient, with R = FR = Z(roots). The group W must be compatible
 with the Cartan matrix C.}
    require IsCartanMatrix(C): "The matrix C needs to be a Cartan matrix";
    require CoxeterMatrix(C) eq CoxeterMatrix(W): "The Cartan matrix is incompatible with the Coxeter matrix.";

    FR := RationalFunctionField(Integers(), Rank(W));

    B := New(BSCat);
    B`C := C;
    B`W := W;
    B`FR := FR;

    // This is where we set up the action of W on the ring R. We take the adjoint root datum and
    // set R = Sym(h*), so that h* has a basis of simple roots (but the simple coroots will be
    // linearly dependent outside of finite type).
    //
    // One further twist: Magma's convention for Cartan matrices is that A_st = <alpha_t^, alpha_s>,
    // which is the transpose of the one used in the Kac-Moody literature, and in the Introduction
    // to Soergel bimodules book. We assume that the given Cartan matrix C is in the Magma convention.
    //
    // s(alpha_t) = alpha_t - <alpha_s^, alpha_t> alpha_s
    //            = alpha_t - a_ts alpha_s
    B`FAct := [ hom< FR -> FR | [FR.t - C[t, s]*FR.s : t in [1..Rank(W)]] > : s in [1..Rank(W)]];

    B`I := [];
    B`Q := FR;
    B`QBase := Rationals();
    B`Spec := hom< FR -> FR | [FR.i : i in [1..Rank(W)]] >;
    B`StdProdSimpleCache := AssociativeArray();
    B`FActionByEltCache := AssociativeArray();
    B`FSpecActionByEltCache := AssociativeArray();
    B`BSActIdCache := AssociativeArray();
    B`BraidCache := AssociativeArray();
    B`meta := AssociativeArray();
    return B;
end intrinsic;

intrinsic BSAntiSpherical(C::AlgMatElt, W::GrpFPCox, aff::RngIntElt) -> BSCat
{The Bott-Samelson category, acting on the antispherical category with aff as the affine root.
This takes R to be the polynomial ring over Z on |C| generators, with Q the rationals.}
    require IsCartanMatrix(C): "The matrix C needs to be a Cartan matrix";
    require CoxeterMatrix(C) eq CoxeterMatrix(W): "The Cartan matrix is incompatible with the Coxeter matrix.";
    require aff in [1 .. Nrows(C)]: "Affine root out of bounds";

    B := BSCategory(C, W);
    B`I := Sort(Setseq({1..Rank(B`W)} diff {aff}));
    B`Q := RationalField();
    B`Spec := hom< B`FR -> B`Q | [(s eq aff) select 1 else 0 : s in [1..Rank(B`W)]] >;
    return B;
end intrinsic;

intrinsic BSParabolic(C::AlgMatElt, W::GrpFPCox, I::SeqEnum[RngIntElt] : allowRationalOpt := true) -> BSCat, GrpFPCox
{}
    require IsCartanMatrix(C): "The matrix C needs to be a Cartan matrix.";
    require CoxeterMatrix(C) eq CoxeterMatrix(W): "The Cartan matrix is incompatible with the Coxeter matrix.";
    require I subset [1..Nrows(C)]: "The parabolic subset is out of bounds.";

    B := BSCategory(C, W);
    B`I := Sort(Setseq({i : i in I}));

    if #B`I eq Rank(B`W) - 1 and allowRationalOpt then
        B`Q := RationalField();
        B`Spec := hom< B`FR -> B`Q | [(s in B`I) select 0 else 1 : s in [1..Rank(B`W)]] >;
    else
        B`Spec := hom< B`FR -> B`FR | [(s in B`I) select 0 else B`FR.s : s in [1..Rank(B`W)]] >;
    end if;

    return B;
end intrinsic;

intrinsic BSFiniteField(C::AlgMatElt, W::GrpFPCox, I::SeqEnum, p::RngIntElt) -> BSCat, GrpFPCox
{}
    require IsPrime(p): "p should be prime, was", p;
    //require #I eq 0: "I should be empty for finite field mode.";

    B := BSCategory(C, W);
    B`I := Sort(Setseq({i : i in I}));

    B`Q := RationalFunctionField(FiniteField(p), Rank(B`W));
    B`QBase := FiniteField(p);
    B`Spec := hom< B`FR -> B`FR | [(s in B`I) select 0 else B`FR.s : s in [1..Rank(B`W)]] >;

    return B;
end intrinsic;


intrinsic FActionByElt(B::BSCat, w::GrpFPCoxElt) -> Map
{The homomorphism B`FR -> B`FR defined by the action of the group element w.}
    if IsDefined(B`FActionByEltCache, w) then
        return B`FActionByEltCache[w];
    end if;

    if #w eq 0 then
        action := hom< B`FR -> B`FR | [B`FR.s : s in [1 .. Rank(B`FR)]] >;
    else
        s := Eltseq(w)[#w];
        action := B`FAct[s] * FActionByElt(B, w * B`W.s);
    end if;

    B`FActionByEltCache[w] := action;
    return action;
end intrinsic;

intrinsic FSpecActionByElt(B::BSCat, w::GrpFPCoxElt) -> Map
{The homomorphism B`FR -> B`Q defined by the action of w followed by specialisation to B`Q.}
    if IsDefined(B`FSpecActionByEltCache, w) then
        return B`FSpecActionByEltCache[w];
    end if;

    action := FActionByElt(B, w) * B`Spec;
    B`FSpecActionByEltCache[w] := action;
    return action;
end intrinsic;

intrinsic Print(B::BSCat)
{}
    printf "Bott-Samelson category on %o generators, specialising to %o", Rank(B`W), B`Q;
end intrinsic;

// Expand a Bott-Samelson object into its full sequence of standard objects.
function ExpandBSObj(B, bsobj)
    std := [B`W.0];
    for s in bsobj do
        std := &cat[[x, x * B`W.s] : x in std];
    end for;
    return std;
end function;

// Internal constructor for BSMor.
// This does mostly the same thing as BSMorphisms, but it only uses expensive checks at higher assert levels.
// Callers should have good reason to believe that these things will be true (anything user-facing cannot
// call this function directly!)
function BSMorConstruct(B, bsdom, bscod, stdmor)
    assert bsdom subset [1..Rank(B`W)];
    assert bscod subset [1..Rank(B`W)];
    assert B`FR eq CoefficientRing(stdmor);
    assert2 ExpandBSObj(B, bsdom) eq Domain(stdmor);
    assert2 ExpandBSObj(B, bscod) eq Codomain(stdmor);

    bsmor := New(BSMor);
    bsmor`Parent := B;
    bsmor`bsdom := bsdom;
    bsmor`bscod := bscod;
    bsmor`stdmor := stdmor;
    return bsmor;
end function;

intrinsic BSMorphism(B::BSCat, bsdom::SeqEnum[RngIntElt], bscod::SeqEnum[RngIntElt], stdmor::StdMor) -> BSMor
{Main constructor for BSMor.}
    require bsdom subset [1..Rank(B`W)]:
        "Domain sequence", bsdom, "has strands outside the range", 1, ":", Rank(B`W);
    require bscod subset [1..Rank(B`W)]:
        "Codomain sequence", bscod, "has strands outside the range", 1, ":", Rank(B`W);
    require ExpandBSObj(B, bsdom) eq Domain(stdmor):
        "Domain expected from Bott-Samelson object", bsdom, "does not match", Domain(stdmor);
    require ExpandBSObj(B, bscod) eq Codomain(stdmor):
        "Codomain expected from Bott-Samelson object", bscod, "does not match", Codomain(stdmor);
    require B`FR eq CoefficientRing(stdmor):
        "Expected coefficient ring", B`FR, "but got", CoefficientRing(stdmor);

    bsmor := New(BSMor);
    bsmor`Parent := B;
    bsmor`bsdom := bsdom;
    bsmor`bscod := bscod;
    bsmor`stdmor := stdmor;
    return bsmor;
end intrinsic;

intrinsic BSMorphism(B::BSCat, bsdom::SeqEnum[RngIntElt], bscod::SeqEnum[RngIntElt], mat::Mtrx : deg := 0) -> BSMor
{Constructor for BSMor where the underlying standard matrix and degree are input directly.}
    stdmor := StdMorphism(ExpandBSObj(B, bsdom), ExpandBSObj(B, bscod), ChangeRing(SparseMatrix(mat), B`FR) : deg := deg);
    return BSMorphism(B, bsdom, bscod, stdmor);
end intrinsic;

intrinsic BSMorphism(B::BSCat, bsdom::SeqEnum[RngIntElt], bscod::SeqEnum[RngIntElt], mat::MtrxSprs : deg := 0) -> BSMor
{Constructor for BSMor where the underlying standard matrix and degree are input directly.}
    stdmor := StdMorphism(ExpandBSObj(B, bsdom), ExpandBSObj(B, bscod), ChangeRing(mat, B`FR) : deg := deg);
    return BSMorphism(B, bsdom, bscod, stdmor);
end intrinsic;

intrinsic Print(f::BSMor)
{}
    printf "Bott-Samelson morphism from %o to %o", f`bsdom, f`bscod;
end intrinsic;

intrinsic Parent(f::BSMor) -> BSCat
{}
    return f`Parent;
end intrinsic;

intrinsic BSId(B::BSCat) -> BSMor
{The identity morphism on the monoidal unit.}
    return BSMorphism(B, [], [], StdMorphism([B`W.0], [B`W.0], IdentitySparseMatrix(B`FR, 1)));
end intrinsic;

intrinsic BSId(B::BSCat, s::RngIntElt) -> BSMor
{The identity morphism Bs -> Bs.}
    require s in [1 .. Rank(B`W)]: "The simple reflection", s, "is not a generator of", B`W;

    return BSId(B, [s]);
end intrinsic;

intrinsic BSId(B::BSCat, bsobj::SeqEnum[RngIntElt]) -> BSMor
{The identity morphism on the Bott-Samelson given by bsobj.}
    require bsobj subset [1..Rank(B`W)]:
        "Sequence", bsobj, "has strands outside the range", 1, ":", Rank(B`W);

    std := ExpandBSObj(B, bsobj);
    return BSMorphism(B, bsobj, bsobj, StdMorphism(std, std, IdentitySparseMatrix(B`FR, #std)));
end intrinsic;

intrinsic CoxeterGroup(f::BSMor) -> GrpFPCox
{Return the Coxeter group the morphism is defined over.}
    return Parent(f)`W;
end intrinsic;

intrinsic CoefficientRing(f::BSMor) -> Rng
{Return the coefficient ring the morphism is defined over.}
    return CoefficientRing(f`stdmor);
end intrinsic;

intrinsic Matrix(f::BSMor) -> Mtrx
{Return the dense matrix underlying f. For interactive or debugging use.}
    return Matrix(f`stdmor);
end intrinsic;

intrinsic 'eq'(f::BSMor, g::BSMor) -> BoolElt
{Check equality of Bott-Samelson morphisms.}
    return (f`bsdom eq g`bsdom) and (f`bscod eq g`bscod) and (f`stdmor eq g`stdmor);
end intrinsic;

intrinsic IsZero(f::BSMor) -> BoolElt
{}
    return IsZero(f`stdmor);
end intrinsic;

intrinsic '*'(r::RngElt, f::BSMor) -> BSMor
{Scale a Bott-Samelson morphism. The element r is coerced into FR, and the degree
of the morphism is adjusted accordingly.}
    B := Parent(f);
    r := B`FR ! r;
    result := BSMorConstruct(B, f`bsdom, f`bscod, r * f`stdmor);
    result`stdmor`deg +:= 2 * TotalDegree(r);
    return result;
end intrinsic;

intrinsic '*'(f::BSMor, g::BSMor) -> BSMor
{Composition (f o g).}
    require f`bsdom eq g`bscod:
        "Domain mismatch while composing Bott-Samelson morphisms:",
        "Left domain is", f`bsdom, "right codomain is", g`bscod;
    return BSMorConstruct(Parent(f), g`bsdom, f`bscod, f`stdmor * g`stdmor);
end intrinsic;

intrinsic 'cat'(f::BSMor, g::BSMor) -> BSMor
{Tensor product of two Bott-Samelson morphisms.}
    B := f`Parent;
    stdmor := Tensor(func< w | FActionByElt(B, w)>, f`stdmor, g`stdmor);
    return BSMorConstruct(B, f`bsdom cat g`bsdom, f`bscod cat g`bscod, stdmor);
end intrinsic;

intrinsic 'cat'(f::BSMor, bsseq::SeqEnum[RngIntElt]) -> BSMor
{Tensor product of the Bott-Samelson morphism f with the identity.}
    // Tensoring on the right by an identity morphism has no twisting involved.
    // We will iterate here using the special InternalTranslateLoc function.
    // (It would be better to have sparse Kronecker products, since then we could
    // just tensor on the right by a sparse identity matrix of the right size).
    W := Parent(f)`W;
    mat := SparseMatrix(f`stdmor`mat);
    for i in [1..#bsseq] do
        InternalTranslateLoc(~mat, [1..Nrows(mat)], [1..Ncols(mat)]);
    end for;

    // TODO: This expanding of domains is very expensive. For example, when calculating
    // C4 with p = 2, just handling these domains accounts for 95% of the running time
    // of this function. If we were to store Bott-Samelson morphisms just with the
    // domain and codomain being sequences of Coxeter generators, this overhead would
    // disappear, and we would only have to expand domains when acting upon the
    // standard category.
    bsstd := ExpandBSObj(Parent(f), bsseq);
    dom := [y * x : x in bsstd, y in f`stdmor`dom];
    cod := [y * x : x in bsstd, y in f`stdmor`cod];

    stdmor := StdMorConstruct(dom, cod, mat, f`stdmor`deg);
    return BSMorConstruct(Parent(f), f`bsdom cat bsseq, f`bscod cat bsseq, stdmor);
    //return f cat BSId(f`Parent, bsseq);
end intrinsic;

intrinsic 'cat'(bsseq::SeqEnum[RngIntElt], g::BSMor) -> BSMor
{Tensor product of the identity with the Bott-Samelson morphism f.}
    bsstd := ExpandBSObj(Parent(g), bsseq);
    dom := [y * x : x in g`stdmor`dom, y in bsstd];
    cod := [y * x : x in g`stdmor`cod, y in bsstd];

    mat := SparseMatrix(Parent(g)`FR, #dom, #cod);
    for i -> w in bsstd do
        InsertBlock(
            ~mat,
            ChangeRing(g`stdmor`mat, FActionByElt(Parent(g), w)),
            (i - 1) * #g`stdmor`dom + 1,
            (i - 1) * #g`stdmor`cod + 1
        );
    end for;

    stdmor := StdMorConstruct(dom, cod, mat, g`stdmor`deg);
    return BSMorConstruct(Parent(g), bsseq cat g`bsdom, bsseq cat g`bscod, stdmor);
end intrinsic;

intrinsic BSAction(I::SeqEnum[RngIntElt], obj::SeqEnum[GrpFPCoxElt], bsobj::SeqEnum[RngIntElt]) -> SeqEnum[GrpFPCoxElt], SeqEnum[RngIntElt]
{The action of a Bott-Samelson object on a standard object, with the Bott-Samelson object action from
the right. This action is considered inside the standard localised-at-I category. The first sequence
returned will be the full list (as if there were no I-quotient). The second sequence returned will be
indices into the first sequence of "surviving" objects.}
    if #obj eq 0 then
        return [], [];
    end if;
    W := Parent(obj[1]);
    prod := obj;
    keep := [true : x in obj];
    for si in bsobj do
        s := W.si;
        newProd := [];
        newKeep := [];
        for i -> x in prod do
            xs := x * s;
            shouldKeep := keep[i] and IsMinimal(I, xs);
            Append(~newProd, x);
            Append(~newProd, xs);
            Append(~newKeep, shouldKeep);
            Append(~newKeep, shouldKeep);
        end for;
        prod := newProd;
        keep := newKeep;
    end for;

    return prod, [i : i -> shouldKeep in keep | shouldKeep], keep;
end intrinsic;

// The anti-spherical action of s on the right of std.
// Returns two sequences: the new standard object, and the indices of the
// original sequence which "survived" under the anti-spherical action.
function simpleObjectAction(B, std, s)
    tuple := <std, s>;
    if IsDefined(B`StdProdSimpleCache, tuple) then
        val := B`StdProdSimpleCache[tuple];
        return val[1], val[2];
    end if;

    Ws := B`W.s;
    newStd := [];
    keepIndices := [];
    for i -> x in std do
        if IsMinimal(B`I, x * Ws) then
            Append(~newStd, x);
            Append(~newStd, x * Ws);
            Append(~keepIndices, i);
        end if;
    end for;

    B`StdProdSimpleCache[tuple] := <newStd, keepIndices>;
    return newStd, keepIndices;
end function;


intrinsic BSAct(B::BSCat, f::StdMor, s::RngIntElt) -> StdMor
{A specialisation of BSAct where the morphism on the right is the identity on a single strand.
This specialisation is a lot faster since we do not have to use the twisted action of one ring
on another (the element on the right consists of 1s and 0s, which are fixed by the action), and
is essentially a Kronecker product with a 2x2 identity matrix on the right, killing some elements
in the domain and codomain first if they are not I-antispherical.}
    require s in [1..Rank(B`W)]:
        "Expected reflection in range", 1, "to", Rank(B`W), "but got", s;
    require CoefficientRing(f) eq B`Q:
        "Expected coefficient ring", B`Q, "for the standard morphism, but got", CoefficientRing(f);

    // Uses some strange custom magma implementation for what is essentially first taking a submatrix,
    // then doing a Kronecker product with a 2x2 identity matrix on the right?
    Ws := B`W.s;
    newDom, domKeep := simpleObjectAction(B, f`dom, s);
    newCod, codKeep := simpleObjectAction(B, f`cod, s);
    mat := f`mat;
    InternalTranslateLoc(~mat, domKeep, codKeep);
    return StdMorConstruct(newDom, newCod, mat, f`deg);
end intrinsic;

intrinsic BSAct(B::BSCat, f::StdMor, bsobj::SeqEnum[RngIntElt]) -> StdMor
{A specialisation of BSAct where the morphism on the right is the identity map on some Bott-Samelson.}
    for s in bsobj do
        f := BSAct(B, f, s);
    end for;
    return f;
end intrinsic;

intrinsic BSAct(B::BSCat, std::SeqEnum[GrpFPCoxElt], s::RngIntElt) -> StdMor
{Act on the identity morphism of a standard sequence, by Bs on the right.}
    return BSAct(B, StdMorphism(B`Q, std), s);
end intrinsic;

intrinsic BSAct(B::BSCat, std::SeqEnum[GrpFPCoxElt], g::BSMor) -> StdMor
{Act on the identity morphism of a standard sequence by g on the right.}
    return BSAct(StdMorphism(B`Q, std), g);
end intrinsic;

intrinsic BSAct(B::BSCat, std::SeqEnum[GrpFPCoxElt], intr::Intrinsic, s::RngIntElt) -> StdMor
{Act on the identity morphism of a standard sequence by intr(B, s) on the right. The call
BSAct(B, std, Unit(B, s)) is equivalent to BSAct(B, std, Unit s), but this function is cached.
The idea is that once we have computed std . Unit(B, s) we re-used it again and again when
translating higher hom spaces. This is a slightly ugly way to get around the issue that actually
computing the action of a BSMor on a StdMor is slow in Magma, even for the special case where
the StdMor is an identity map.}
    tup := <std, intr, s>;
    if IsDefined(B`BSActIdCache, tup) then
        return B`BSActIdCache[tup];
    end if;

    result := BSAct(StdMorphism(B`Q, std), intr(B, s));
    B`BSActIdCache[tup] := result;
    return result;
end intrinsic;

// For whatever reason, the sparse submatrix code up to v2.25-8 is very slow for the case where few rows and
// columns are deleted, and the sparse submatrix code in v2.25-9 is broken. We will use this version in the
// mean time, but it should be replaced by Submatrix(M, I, J) when a good patch comes for magma.
function SubmatrixDeleting(M, I, J)
    assert I eq Sort(I);
    assert J eq Sort(J);

    for i in [i : i in [Nrows(M) .. 1 by -1] | i notin I] do
        RemoveRow(~M, i);
    end for;

    for j in [j : j in [Ncols(M) .. 1 by -1] | j notin J] do
        RemoveColumn(~M, j);
    end for;

    return M;
end function;

intrinsic BSAct(f::StdMor, g::BSMor) -> StdMor
{The action of the Bott-Samelson morphism on the standard morphism. If I is nonempty, it is the "anti-spherical"
action (or more generally a parabolic action). The function act should be a map W x R -> S, where R is the
coefficient ring of the Bott-Samelson morphism, and S is the coefficient ring of the standard morphism.}
    B := g`Parent;
    require CoefficientRing(f) eq B`Q:
        "Expected coefficient ring", B`Q, "for the standard morphism, but got", CoefficientRing(f);

    dom, domIndices, domKeep := BSAction(B`I, f`dom, g`bsdom);
    cod, codIndices, codKeep := BSAction(B`I, f`cod, g`bscod);
    newMat := SparseMatrix(B`Q, #dom, #cod);

    for left in Eltseq(f`mat) do
        for right in Eltseq(g`stdmor`mat) do
            i := (left[1] - 1) * #g`stdmor`dom + right[1];
            j := (left[2] - 1) * #g`stdmor`cod + right[2];
            if domKeep[i] and codKeep[j] then
                w := f`dom[left[1]];
                r := right[3];
                SetEntry(~newMat, i, j, left[3] * FSpecActionByElt(B, w)(r));
            end if;
        end for;
    end for;

    // We should be right to use the internal StdMorConstruct constructor: our action should not have
    // put any matrix entries in unsupported places.
    return StdMorConstruct(
        [dom[i] : i in domIndices],
        [cod[i] : i in codIndices],
        SubmatrixDeleting(newMat, domIndices, codIndices),
        f`deg + g`stdmor`deg
    );
end intrinsic;

intrinsic IsCoercible(B::BSCat, x::.) -> BoolElt
{}
    if Type(x) eq BSMor then
        return true, x;
    end if;

    return false;
end intrinsic;


// The following definitions are straight out of "Localized Calculus for the Hecke Category" by
// Elias and Williamson. These define the generating morphisms (and some other auxiliary morphisms such
// as cups and caps) in the full localised category with no parabolic quotient. Our matrix conventions
// are the transpose of those in the paper: for us, the domain corresponds to the rows and the codomain
// to the columns. For more details (especially on the spider and braid morphisms) we refer the reader
// to the paper.

intrinsic Counit(B::BSCat, s::RngIntElt) -> BSMor
{The dot morphism Bs -> 1.}
    a := B`FR.s;
    return BSMorphism(B, [s], [], Matrix([[a], [0]]) : deg := 1);
end intrinsic

intrinsic Unit(B::BSCat, s::RngIntElt) -> BSMor
{The dot morphism 1 -> Bs.}
    return BSMorphism(B, [], [s], Matrix([[1, 0]]) : deg := 1);
end intrinsic

intrinsic Comult(B::BSCat, s::RngIntElt) -> BSMor
{The trivalent vertex Bs -> Bs Bs.}
    a := B`FR.s;
    return BSMorphism(B, [s], [s, s], Matrix([
        [1/a,   0,    0, -1/a],
        [0,   1/a, -1/a,    0]
    ]) : deg := -1);
end intrinsic;

intrinsic Mult(B::BSCat, s::RngIntElt) -> BSMor
{The trivalent vertex Bs Bs -> Bs.}
    return BSMorphism(B, [s, s], [s], Matrix([
        [1, 0],
        [0, 1],
        [0, 1],
        [1, 0]
    ]) : deg := -1);
end intrinsic;

intrinsic Cap(B::BSCat, s::RngIntElt) -> BSMor
{The cap Bs Bs -> 1.}
    a := B`FR.s;
    return BSMorphism(B, [s, s], [], Matrix([
        [a], [0], [0], [a]
    ]) : deg := 0);
end intrinsic;

intrinsic Cup(B::BSCat, s::RngIntElt) -> BSMor
{The cup 1 -> Bs Bs.}
    a := B`FR.s;
    return BSMorphism(B, [], [s, s], Matrix([
        [1/a, 0, 0, -1/a]
    ]) : deg := 0);
end intrinsic;

intrinsic Spider(B::BSCat, s::RngIntElt, t::RngIntElt) -> BSMor
{The "spider" morphism from Bs Bt Bs ... (tensor) Bt Bs Bt ... -> 1, called E_st.}
    W := B`W;
    m := CoxeterMatrix(W)[s, t];
    require m ne 0: "s and t must have finite order.";

    // word = ststs... for a length of 2m.
    word := &cat[[s, t] : i in [1 .. m]];
    pi := &*[FActionByElt(B, W ! word[1..i-1])(B`FR.(word[i])) : i in [1..m]];

    // Place pi into (row, column) spots corresponding to the identity.
    dom := BSAction([], [W.0], word);
    mat := SparseMatrix(B`FR, #dom, 1);
    for i -> x in dom do
        if x eq W.0 then
            mat[i, 1] := pi;
        end if;
    end for;

    return BSMorphism(B, word, [], mat : deg := 0);
end intrinsic;

intrinsic Braid(B::BSCat, s::RngIntElt, t::RngIntElt) -> BSMor
{The 2m_st-valent vertex Bs Bt ... -> Bt Bs ...}
    if IsDefined(B`BraidCache, <s, t>) then
        return B`BraidCache[<s, t>];
    end if;

    m := CoxeterMatrix(B`W)[s, t];
    require m ge 2: "s and t must have finite order.";

    spider := Spider(B, s, t);
    stst := &cat[[s, t] : i in [1..m]];
    first := stst[1..m];
    second := stst[m+1..2*m];

    // Build a series of nested cups, from bottom to top, outside to inside..
    nest := &*[
        second[1..i-1] cat Cup(B, second[i]) cat Reverse(second[1..i-1])
        : i in Reverse([1..m])
    ];

    braid := &*[
        spider cat Reverse(second),
        first cat nest
    ];
    B`BraidCache[<s, t>] := braid;
    return braid;
end intrinsic;

intrinsic BraidUp(B::BSCat, bsword::[RngIntElt], i::RngIntElt, j::RngIntElt) -> BSMor
{Let i < j, and bsword[i..j] be of the form [st...] for m_st = j - i + 1. Return a
 braiding morphism from prefix.[st...].suffix to prefix.[ts...].suffix. }
    require 1 le i and i lt j and j le #bsword: "i =", i, "or j =", j, "out of bounds";
    s := bsword[i];
    t := bsword[i+1];
    mst := Order((B`W.s) * (B`W.t));
    require mst eq j - i + 1: "m_st incorrect";

    // If anything else is out of place, we should get a failure while composing morphisms.
    return bsword[1..i-1] cat Braid(B, s, t) cat bsword[j+1..#bsword];
end intrinsic;

intrinsic BraidDown(B::BSCat, bsword::[RngIntElt], i::RngIntElt, j::RngIntElt) -> BSMor
{Let i < j, and bsword[i..j] be of the form [st...] for m_st = j - i + 1. Return a
 braiding morphism from prefix.[ts...].suffix to prefix.[st...].suffix. }
    s := bsword[i];
    t := bsword[i+1];
    for k in [i..j] do
        bsword[k] := bsword[k] eq s select t else s;
    end for;
    return BraidUp(B, bsword, i, j);
end intrinsic;
