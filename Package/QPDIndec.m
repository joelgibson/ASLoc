declare type QPDI;
declare attributes QPDI:
    Parent,    // BSCat,
    elt,       // GrpFPCoxElt - The element/alcove corresponding to this indecomposable.
    character, // The Hecke algebra element corresponding to this alcove, in the canonical basis.
    stdSeq,    // Our chosen standard sequence for the indecomposable.

    // homsIn is an associative array indexed by antispherical Weyl group elements. For each
    // element w, homsIn[w] is a sequence of StdMors. These StdMors descend to a basis for the hom
    // space Hom_{>= w}(D_w, D_elt), where D_elt is the current indecomposable. (The homs themselves
    // do not live in the quotient, they are just selected so that when the quotient {>= w} is performed,
    // they are a basis).
    // homsOut is likewise, but represents a basis for the space Hom_{>= w}(D_elt, D_w).
    homsIn,    // A basis for the hom-space from all lower alcoves to this one.
    homsOut,   // A basis for the hom-space from this one to all lower alcoves.

    // Suppose that s is in the right parabolic descent set of alcove, so that
    // length(alcove . s) + 1 = length(alcove). Let I(alcove . s) and I(alcove) be
    // the two standard objects we have chosen to represent the indecomposables, then
    // incl[s]: I(alcove) -> I(alcove . s) B(s) and proj[s]: I(alcove . s) B(s) -> I(alcove)
    // are the inclusions and projections realising the big summand in I(alcove . s) B(s).
    //
    // This is a different convention than used in pDIndec: the projections and inclusion
    // belonging for an alcove are to and from the stdSeq for that alcove, and the
    // Bs.(descendents).
    incl, proj;

intrinsic Print(QI::QPDI)
{}
    printf "Indecomposable object for element %o", QI`elt;
end intrinsic;


intrinsic TrivialQPDI(B::BSCat, ASMod::FModIHke) -> QPDI
{Create the trivial indecomposable for the category, corresponding to the identity alcove.}
    id := B`W.0;

    QI := New(QPDI);
    QI`Parent := B;
    QI`elt := id;
    QI`character := StandardBasis(ASMod).0;
    QI`stdSeq := [id];
    QI`homsIn := AssociativeArray();
    QI`homsIn[id] := [StdMorphism(B`Q, [id])];
    QI`homsOut := AssociativeArray();
    QI`homsOut[id] := [StdMorphism(B`Q, [id])];
    QI`incl := AssociativeArray();
    QI`proj := AssociativeArray();
    return QI;
end intrinsic;

intrinsic QCanonicalRex(B::BSCat, w::GrpFPCoxElt) -> SeqEnum[RngIntElt]
{Return the canonical rex of an element.}
    return Eltseq(w);
end intrinsic;

intrinsic calcQIndec(B::BSCat, indecs::Assoc, newElt::GrpFPCoxElt, p::RngIntElt, HAlg::FModIHke, ASMod::FModIHke) -> QPDI
{Calculate the modular indecomposable object corresponding to the alcove. In order for this
function to succeed, all other "relevant" (whatever happens to be needed) indecomposables must
have already be calculated, and available in the indecs associative array - otherwise the
computation will fail.

Internally, this function calculates the p-canonical basis element in terms of the canonical basis
in two different ways. The first is by keeping track of the smaller idempotents removed from
old . Bs, and the second is the character map (graded ranks of the final hom spaces). An error will
be thrown if these two methods do not agree. The basis element is stored on indec`character.}
    W := B`W;
    v := BaseRing(HAlg).1;
    C := CanonicalBasis(HAlg);
    aC := CanonicalBasis(ASMod);

    // For the identity, just return a new trivial object.
    if newElt eq W.0 then
        return TrivialQPDI(B, ASMod);
    end if;

    // Otherwise, find a previous object and move it up.
    // Let s be the ending letter for the canonical rex for newElt. The object we choose to move
    // up is prevElt = newElt * s.
    s := QCanonicalRex(B, newElt)[#newElt];
    prevElt := newElt * W.s;
    error if not IsDefined(indecs, prevElt),
        "Need to have calculated the indecomposable for", prevElt, "before", newElt;

    prevQI := indecs[prevElt];

    // Get the homs in and out, and the identity endomorphism, for prevElt . Bs
    homsIn, homsOut := QtranslateIndecObj(B, indecs, prevElt, s);
    identity := BSAct(B, prevQI`stdSeq, s);

    // The previous canPol gives the graded support of prevQI. Right-multiplying by Can(s) and
    // subtracting off the top term gives us the graded support of everything we might need to remove.
    lowerTerms := prevQI`character * C.s - aC.newElt;
    idem, removed := QReduceIdempotent(B, lowerTerms, homsIn, homsOut, identity, p);

    // Record the term we just subtracted from canPol.
    removedPol := (#removed eq 0)
        select aC ! 0
        else &+[indecs[pair[1]]`character * v^pair[2] : pair in removed];

    // Now we should have the p-canonical basis element, expressed in the canonical basis.
    canPol := prevQI`character * C.s - removedPol;

    // We decompose the idempotent arbitrarily into an inclusion from some standard sequence,
    // and a projection back to that standard sequence.
    proj, incl := DecomposeIdem(idem);

    assert2 IsOne(proj * incl);
    assert2 incl * proj eq idem;

    // Since we want to end up with morphisms to B(prevElt . s), not B(prevElt) . Bs, we
    // need to adjust the morphisms we have so far with the inclusion and projection maps.
    // For the morphisms in, we need to postcompose with projection. For the morphisms out,
    // we need to precompose with inclusion. For the endomorphisms of the top alcove, we need
    // to do both.
    truncHomsIn, truncHomsOut := TruncateHomsInOut(proj, incl, homsIn, homsOut, newElt);

    // Now that we have truncated, the morphisms might have become linearly dependent. We need to
    // trim them back to what they should be.
    prunedHomsIn, prunedHomsOut := QPruneHomsInOut(B, truncHomsIn, truncHomsOut, p);

    // As a sanity check, we can calculate the canPol in a different way, using the character map.
    characterIn := GetCharacter(B, prunedHomsIn, ASMod);
    characterOut := GetCharacter(B, prunedHomsOut, ASMod);
    error if characterIn ne characterOut,
        "Characters in and out disagree\n",
        "Character calculated using homsIn was", characterIn,
        "Character calculated using homsOut was", characterOut;
    error if characterIn ne canPol,
        "p-canonical basis element calculated using removal disagrees with character map\n",
        "Using removal:", canPol,
        "Character map:", characterIn;

    // Our object is almost complete, we just need to compute the extra incl and proj maps.
    QI := New(QPDI);
    QI`Parent := B;
    QI`elt := newElt;
    QI`character := canPol;
    QI`stdSeq := Domain(incl);
    QI`homsIn := prunedHomsIn;
    QI`homsOut := prunedHomsOut;
    QI`incl := AssociativeArray();
    QI`proj := AssociativeArray();
    QI`incl[s] := incl;
    QI`proj[s] := proj;

    // Iterate over all s in the right parabolic descent set of alcove, minus the generator
    // we have already taken care of.
    rds := {t : t in RightDescentSet(W, newElt) | IsMinimal(B`I, newElt * W.t)} diff {s};
    for t in rds do
        prevAlcoveElt := newElt * W.t;
        prevQI := indecs[prevAlcoveElt];

        homsIn, homsOut := QtranslateIndecObj(B, indecs, prevAlcoveElt, t);
        identity := BSAct(B, prevQI`stdSeq, t);

        // The previous canPol gives the graded support of prevQI. Right-multiplying by Can(t) and
        // subtracting off the top term gives us the graded support of everything we might need to remove.
        tLowerTerms := prevQI`character * C.t - aC.newElt;
        idem := QReduceIdempotent(B, tLowerTerms, homsIn, homsOut, identity, p);

        // We decompose the idempotent arbitrarily into an inclusion from some standard sequence,
        // and a projection back to that standard sequence.
        tproj, tincl := DecomposeIdem(idem);

        assert2 IsOne(tproj * tincl);
        assert2 tincl * tproj eq idem;

        // tincl and tproj give realisations of an isomorphic standard object as incl and proj, but
        // not equal. We will build a base change map going from the standard object choice ending
        // in s to the standard object choice ending in t.
        //
        // This map is built as follows; for example's sake assume that m_st = 3. Let x be the minimal
        // coset representative for the right action of {s, t} on newAlcove. We then can get back up to
        // newAlcove in two different ways:
        //    newAlcove = x . sts, which is the "rex ending in s" or rexs.
        //    newAlcove = x . tst, which is the "rex ending in t" or rext.
        // Up above, we have computed the stdSeq for newAlcove by using the rex ending in s, along with
        // inclusions and projections
        //    stdSeq_s (-> incl ->) B(xst) B(s) (-> proj ->) stdSeq_s
        // Just now, we have computed the corresponding inclusions and projections for xtst, which are
        // out of and into a different standard sequence generated by acting on the right by t:
        //    stdSeq_t (-> tincl ->) B(xst) B(s) (-> tproj ->) stdSeq_t
        // The base change map will be a map from stdSeq_s to stdSeq_t built out of three inclusions,
        // followed by a braid move (the 2m_st-valent vertex), followed by three projections. In terms
        // of objects, the sequence of inclusions goes
        //   stdSeq_s = B(x sts) -> B(x st) B(s) -> B(x s) B(s) B(t) -> B(x) B(s) B(t) B(s)
        //            incl = incl[xsts][s]    incl[xst][t] B(t)   incl[xs][s] B(t) B(s)
        // We then act on the right of B(s) with the 2m_st-valent vertex, taking us from
        //   B(x) B(s) B(t) B(s) -> B(x) B(t) B(s) B(t)
        // The sequence of projections is then basically the reverse of the sequence of inclusions,
        // ending the the projection tproj.
        //
        // If we have done this right, the composite baseChange map will be an isomorphism from the
        // standard sequence ending s to the standard sequence ending t, which we can use to rewrite
        // our hom spaces into just stdSeq_s.
        minElt, rexs := MinimalLeftRep(W, newElt, {s, t}, s);
        minElt, rext := MinimalLeftRep(W, newElt, {s, t}, t);
        minQI := indecs[minElt];
        baseChange := &*&cat[
            [tproj],
            [BSAct(
                B,
                indecs[minElt * (W ! rext[1..i])]`proj[rext[i]],
                rext[i+1..m]
            )
                : i in [m-1 .. 1 by -1]
            ] where m := #rext,
            [BSAct(B, minQI`stdSeq, Braid(B, rexs[1], rexs[2]))],
            [BSAct(
                B,
                indecs[minElt * (W ! rexs[1..i])]`incl[rexs[i]],
                rexs[i+1..m]
            )
                : i in [1..m-1]
            ] where m := #rexs,
            [incl]
        ];

        QI`incl[t] := tincl * baseChange;
        QI`proj[t] := Inverse(baseChange) * tproj;
    end for;
    return QI;
end intrinsic;

// This function is split out of the main calculation so that we can track how long it's taking
// in the profiler.
intrinsic TruncateHomsInOut(proj::StdMor, incl::StdMor, homsIn::Assoc, homsOut::Assoc, topAlcove::GrpFPCoxElt) -> Assoc, Assoc
{Precompose with inclusion for morphisms going in, postcompose with projection for morphisms going out.
On the top alcove, do both.}
    truncHomsIn := AssociativeArray();
    truncHomsOut := AssociativeArray();
    for smallAlcove in Keys(homsIn) diff {topAlcove} do
        truncHomsIn[smallAlcove] := [proj * mor : mor in homsIn[smallAlcove]];
        truncHomsOut[smallAlcove] := [mor * incl : mor in homsOut[smallAlcove]];
    end for;
    truncHomsIn[topAlcove] := [proj * mor * incl : mor in homsIn[topAlcove]];
    truncHomsOut[topAlcove] := [proj * mor * incl : mor in homsOut[topAlcove]];

    return truncHomsIn, truncHomsOut;
end intrinsic;

intrinsic QReduceIdempotent(B::BSCat, ch::EltIHke, homsIn::Assoc, homsOut::Assoc, idem::StdMor, p::RngIntElt) -> StdMor, SetMulti
{Reduce the idempotent, returning the reduced idempotent and a multiset of <alcove, degree> pairs removed.}
    elts, coeffs := Support(ch);
    // elts := Sort(Setseq(Support(ch)));
    // coeffs := [Coefficient(ch, w) : w in elts];
    removed := {* *}; // Multiset of alcoves we removed.
    for eltIndex in [1..#elts] do
        coeffSeq, val, _ := Coefficients(coeffs[eltIndex]);
        degreeSeq := [ val + deg - 1 : deg in [1..#coeffSeq] | coeffSeq[deg] ne 0];
        alcoveElt := elts[eltIndex];
        inDegs := [ll`deg : ll in homsIn[alcoveElt]];
        outs := homsOut[alcoveElt];
        ins := homsIn[alcoveElt];

        for curDeg in degreeSeq do
            if (curDeg le 0) and ({curDeg, -curDeg} subset Seqset(inDegs)) then
                // If p > 0, compute the intersection form modulo p to count the number of times we need to reduce.
                // Otherwise, just calculate the rank.
                IF := (p ne 0)
                    select ChangeRing(QIntersectionForm(outs, idem, ins, curDeg), FiniteField(p))
                      else ChangeRing(QIntersectionForm(outs, idem, ins, curDeg), Rationals());


                // Since we just took out a summand of kind smdI from the big (current) object,
                // we will have changed the morphism spaces so we need to correct them later.
                // Any object smaller than smdI also has a morphism space to newI which now needs
                // to be changed.
                for k in [1..Rank(IF)] do
                    summand := QreduceOnceAt(B, outs, idem, ins, curDeg, p);
                    idem := idem + (-summand);
                    Include(~removed, <alcoveElt, curDeg>);

                    if curDeg ne 0 then
                        summand := QreduceOnceAt(B, outs, idem, ins, -curDeg, p);
                        idem := idem + (-summand);
                        Include(~removed, <alcoveElt, -curDeg>);
                    end if;
                end for;
            end if;
        end for;
    end for;

    return idem, removed;
end intrinsic;


intrinsic QreduceOnceAt(B::BSCat, homsOut::SeqEnum[StdMor], idem::StdMor, homsIn::SeqEnum[StdMor], degree::RngIntElt, p::RngIntElt) -> StdMor
{Reduce a q-idempotent at an alcove in degree d.}
    homsIn := [ll : ll in homsIn | ll`deg eq degree];
    homsOut := [ll : ll in homsOut | ll`deg eq -degree];

    // If we are working with a general parabolic, the matrix entries should be rational numbers, but
    // living inside a function field in several variables. ChangeRing will throw an error if any entries
    // still contain indeterminates.
    IF := ChangeRing(QIntersectionForm(homsOut, idem, homsIn, degree), B`QBase);

    // If p > 0, find an entry of the intersection form which is invertible over the p-adics.
    // Otherwise, find any nonzero entry.
    if p ne 0 and Characteristic(BaseRing(B`Q)) eq 0 then
        pair := rep{<row, col> : col in [1..#homsOut], row in [1..#homsIn] | Valuation(IF[row][col], p) eq 0};
    else
        pair := rep{<row, col> : col in [1..#homsOut], row in [1..#homsIn] | IF[row][col] ne 0};
    end if;

    // Get the light leaves and create the idempotent.
    // Big sum (-> down ->) alcove (-> up ->) Big sum
    down := homsOut[pair[2]] * idem;
    up := idem * homsIn[pair[1]];
    idem := up * Inverse(down * up) * down;

    assert2 idem * idem eq idem;
    return idem;
end intrinsic;

intrinsic QIntersectionForm(LLsOut::SeqEnum[StdMor], idem::StdMor, LLsIn::SeqEnum[StdMor], degree::RngIntElt) -> AlgMatElt
{Returns the local intersection form of LLsOut and LLsIn in the given degree. Let x <= y so that
LLsOut: y -> x and LLsIn: x -> y. Then the [i, j] entry of the intersection form is (in[i] o out[j]),
projected to the >= x local category.}
    LLsIn := [ ll : ll in LLsIn | ll`deg eq degree];
    LLsOut := [ ll : ll in LLsOut | ll`deg eq -degree];

    IF := ZeroMatrix(CoefficientRing(idem), #LLsIn, #LLsOut);
    for i -> qin in LLsIn do
        for j -> qout in LLsOut do
            // Take the lower right entry. The lower right entry should be the top term
            // in the Bruhat order for all elements appearing in this standard sequence,
            // so only looking at that entry essentially computes the intersection form
            // in the >= quotient.
            n := Nrows(qin`mat);
            prod := RowSubmatrix(qin`mat, n, 1) * idem`mat * ColumnSubmatrix(qout`mat, n, 1);

            assert Nrows(prod) eq 1 and Ncols(prod) eq 1;
            IF[i, j] := prod[1, 1];
        end for;
    end for;

    return IF;
end intrinsic;


intrinsic QtranslateIndecObj(B::BSCat, indecs::Assoc, X::GrpFPCoxElt, s::RngIntElt) -> pDIndec
{Return the LLsIn and LLsOut for I . Bs}
    W := B`W;

    // IMPORTANT NOTE
    // Throughout this function we use short names for group elements (anything else is more confusing).
    // X is an element such that X < Xs. The letter Y later on will refer to a hom space Hom(Y, X).
    XIndec := indecs[X];

    // The variable "alcove" is used below, I should rename the one below to "smallAlcove" or something.
    Xs := X * W.s;
    require s notin RightDescentSet(W, X):
            "The given indecomposable object has to be taken up by s!";
    require IsMinimal(B`I, Xs):
            "The element is taken out of the antispherical region.";

    newIRex := QCanonicalRex(B, Xs);

    // Create the Q-lightleaves
    newQLLsIn := AssociativeArray();
    newQLLsOut := AssociativeArray();

    // Translate all light leaves of I. "alcove" is the small object below I, so that the
    // light leaves are in: alcove -> I and out: I -> alcove. Make sure we iterate over all of the alcoves in
    // increasing order of length so that the resulting homs come out in a deterministic order.
    for Y in Sort(Setseq(Keys(XIndec`homsIn))) do
        error if not IsDefined(indecs, Y),
            "Should have already calculated", Y;

        // If newAlcove = alcove . s leaves the antispherical region, it does not
        // participate any further.
        Ys := Y * W.s;
        if not IsMinimal(B`I, Ys) then
            continue;
        end if;

        // From here on, we have that alcove . s = newAlcove, and
        // alcove and newAlcove are distinct antispherical alcoves. Since they
        // differ by a reflection, they are comparable in the Bruhat order.


        // Prepare the associative arrays for the new data to be added
        if not IsDefined(newQLLsIn, Y) then
            newQLLsIn[Ys] := [];
            newQLLsIn[Y] := [];
            newQLLsOut[Ys] := [];
            newQLLsOut[Y] := [];
        end if;

        // Do the light leaves inductive construction.
        if BruhatLessOrEqual(W, Y, Ys) then
            // Light leaf cases where Y < Ys: 1U and 0U
            stdSeq := indecs[Y]`stdSeq;
            qdDot := BSAct(B, stdSeq, Unit, s);   // Cached version of BSAct(B, stdSeq, Unit(B, s));
            qiDot := BSAct(B, stdSeq, Counit, s); // Cached version of BSAct(B, stdSeq, Counit(B, s));
            for i in [1..#XIndec`homsIn[Y]] do
                // Act on both homs on the right by Bs.
                inhomBs := BSAct(B, XIndec`homsIn[Y][i], s);
                outhomBs := BSAct(B, XIndec`homsOut[Y][i], s);

                // First go up (U1)
                if Y eq X then
                    // If alcove = bigAlcove, then newAlcove is the alcove that we are
                    // translating into. There are no projections here yet, so simply
                    // append the new morphisms.
                    Append(~newQLLsIn[Ys], inhomBs);
                    Append(~newQLLsOut[Ys], outhomBs);
                else
                    // Otherwise, we should truncate the morphism so we are only considering
                    // the indecomposable object associated to newAlcove.
                    Append(~newQLLsIn[Ys], inhomBs * indecs[Ys]`incl[s]);
                    Append(~newQLLsOut[Ys], indecs[Ys]`proj[s] * outhomBs);
                end if;

                // Now go down (U0).
                Append(~newQLLsIn[Y], inhomBs * qdDot);
                Append(~newQLLsOut[Y], qiDot * outhomBs);
            end for;
        else
            // Light leaf cases where Y > Ys: 0D and 1D
            // YRex := QCanonicalRex(B, Y);

            inclTrans := BSAct(B, indecs[Y]`incl[s], s);
            projTrans := BSAct(B, indecs[Y]`proj[s], s);

            basis := indecs[Ys]`stdSeq;
            comult := BSAct(B, basis, Comult, s); // Cached version of BSAct(B, basis, Comult(B, s))
            mult := BSAct(B, basis, Mult, s);     // Cached version of BSAct(B, basis, Mult(B, s))
            unit := BSAct(B, basis, Unit, s);
            counit := BSAct(B, basis, Counit, s);

            for i in [1..#XIndec`homsIn[Y]] do
                // Act on both homs on the right by Bs.
                inhomBs := BSAct(B, XIndec`homsIn[Y][i], s);
                outhomBs := BSAct(B, XIndec`homsOut[Y][i], s);

                // Extract the "common core" of both
                inCore := inhomBs * projTrans * comult;
                outCore := mult * inclTrans * outhomBs;

                // (D1)
                Append(~newQLLsIn[Y], inCore * indecs[Y]`incl[s]);
                Append(~newQLLsOut[Y], indecs[Y]`proj[s] * outCore);

                // Then: We move down
                // Since the codimension is 1, there should be exactly one incoming
                // (resp. outgoing) light leaf newAlcove -> alcove
                // (resp. alcove -> newAlcove) consisting of a dot
                // require IsDefined(indecs[Y]`homsIn, Ys) and (#indecs[Y]`homsIn[Ys] eq 1) and
                //         IsDefined(indecs[Y]`homsOut, Ys) and (#indecs[Y]`homsOut[Ys] eq 1):
                //         "These light leaves should be defined!";

                // Store the new light leaves
                Append(~newQLLsIn[Ys], inCore * unit);    // In
                Append(~newQLLsOut[Ys], counit * outCore); // Out
            end for;
        end if;
    end for;

    assert Keys(newQLLsIn) eq Keys(newQLLsOut);
    assert &and[#newQLLsIn[key] eq #newQLLsOut[key] : key in Keys(newQLLsIn)];
    return newQLLsIn, newQLLsOut;
end intrinsic;

intrinsic MinimalLeftRep(W::GrpFPCox, x::GrpFPCoxElt, refls::SetEnum, s::RngIntElt) -> GrpFPCoxElt, SeqEnum
{Given an element x, two reflections [s, t], and the reflection s which ends a rex for x, return
w, rex where w * rex = x, and rex ends in s.}
    require #refls eq 2: "This function only works with two simple reflections.";
    require s in refls: "The simple reflection", s, "given was not an element of the reflection set", refls;
    require refls subset RightDescentSet(W, x): "The reflections", refls, "were not in the right descent set";

    t := Rep(refls diff {s});
    m := CoxeterMatrix(W)[s, t];
    require m ge 2: "The subgroup generated by", refls, "is infinite.";

    rexinv := (&cat[[s, t] : _ in [1 .. m]])[1..m];
    rex := Reverse(rexinv);
    w := x * (W ! rexinv);

    assert IsEmpty(RightDescentSet(W, w) meet refls);
    assert w * (W ! rex) eq x;

    return w, rex;
end intrinsic;

intrinsic QPruneHomsInOut(B::BSCat, homsIn::Assoc, homsOut::Assoc, p::RngIntElt) -> Assoc, Assoc
{}
    newHomsIn := AssociativeArray();
    newHomsOut := AssociativeArray();
    for elt in Keys(homsIn) do
        lowerStdSeq := Domain(homsIn[elt][1]);
        upperStdSeq := Codomain(homsIn[elt][1]);

        // This QuotientIncl is one of the most expensive calculations we do: it essentially
        // compares elt against every element of upperStdSeq in the Bruhat order, and keeps
        // only the terms >= elt.
        outIncl := QuotientIncl(B`Q, upperStdSeq, elt);
        inProj := Transpose(outIncl);

        assert forall{1 : w in lowerStdSeq[1..#lowerStdSeq - 1] | #w lt #elt} and lowerStdSeq[#lowerStdSeq] eq elt;

        quotHomsIn := [inProj * LimitDomain(f, #lowerStdSeq) : f in homsIn[elt]];
        newIn := homsIn[elt][QIndepIndices(B, quotHomsIn, p)];
        if #newIn gt 0 then
            newHomsIn[elt] := newIn;
        end if;

        quotHomsOut := [LimitCodomain(f, #lowerStdSeq) * outIncl : f in homsOut[elt]];
        newOut := homsOut[elt][QIndepIndices(B, quotHomsOut, p)];
        if #newOut gt 0 then
            newHomsOut[elt] := newOut;
        end if;
    end for;

    return newHomsIn, newHomsOut;
end intrinsic;

intrinsic QuotientIncl(R::Rng, obj::SeqEnum[GrpFPCoxElt], minElt::GrpFPCoxElt) -> StdMor
{Give the inclusion map (x in obj | minElt <= x) into obj, over the given base ring.}

    // We could do this construction with list comprehensions, but we lose the profiling
    // information about BruhatLessOrEqual if it's the comprehension calling it.
    W := Parent(minElt);
    inclMat := SparseMatrix(R, 0, #obj);
    dom := [];
    for j -> x in obj do
        if BruhatLessOrEqual(W, minElt, x) then
            Append(~dom, x);
            SetEntry(~inclMat, Nrows(inclMat) + 1, j, 1);
        end if;
    end for;
    return StdMorphism(dom, obj, inclMat);
end intrinsic;

intrinsic QIndepIndices(B::BSCat, homs::SeqEnum[StdMor], p::RngIntElt) -> SeqEnum[RngIntElt]
{Given a set of homs (treated as a set of graded morphisms over a nonnegatively graded algebra),
return a subsequence S such that homs[S] is independent over the graded algebra.}
    if #homs eq 0 then
        return [];
    end if;

    V := VectorSpace(B`Q, Maximum({#Domain(homs[1]), #Codomain(homs[1])}));

    // Partition the hom space by degree.
    degrees := Sort({@ ll`deg : ll in homs @});
    homsByDeg := AssociativeArray();
    indicesByDeg := AssociativeArray();
    for i -> ll in homs do
        if not IsDefined(homsByDeg, ll`deg) then
            homsByDeg[ll`deg] := [];
            indicesByDeg[ll`deg] := [];
        end if;
        Append(~homsByDeg[ll`deg], ll);
        Append(~indicesByDeg[ll`deg], i);
    end for;

    // We'll need to record the previous bases for different degrees.
    newIndices := [];
    prevBases := [];

    for deg in degrees do
        Vquo, f := quo< V | prevBases >;
        quotLLVects := [];
        basis := [];
        quotBasis := [];
        for ll in homsByDeg[deg] do
            v := V!Matrix(Vector(Matrix(ll)));
            Append(~quotLLVects, f(v));

            if IsIndependent(Append(quotBasis, f(v))) then
                Append(~basis, v);
                Append(~quotBasis, f(v));
            end if;
        end for;

        // Express all light leaf vectors in quotBasis and choose a spanning set over Zp
        if #quotBasis gt 0 then
            spanningVectors := [ Vector([B`Q!coeff: coeff in ExpressInBasis(v, quotBasis)]) :
                                v in quotLLVects];

            valSpanningSet := QValuationSpanningSubset(spanningVectors, p);
        else
            valSpanningSet := [Integers() | ];
        end if;

        newIndices cat:= indicesByDeg[deg][valSpanningSet];

        prevBases cat:= basis;
    end for;

    return newIndices;
end intrinsic;

intrinsic ExpressInBasis(v::ModTupFldElt, basis::SeqEnum) -> SeqEnum
{Express the sparse matrix in the given basis and return the sequence of coefficients.}
    require #basis gt 0: "inBasis was given the empty basis!";
    require Parent(basis[1]) eq Parent(v): "The given elements don't lie in the same vector space!";

    sol := Solution(Matrix(#basis, #Eltseq(basis[1]), basis), v);
    return Eltseq(sol);
end intrinsic;

intrinsic QValuationSpanningSubset(Vects::SeqEnum[ModTupFldElt], p::RngIntElt) -> SeqEnum
{Given a sequence of vectors return a subset of indices yielding a basis of the span of Vects over Z_p.}
    rank := Rank(Matrix(Vects));
    X := [j : j in [1..#Vects]];

    for a in [rank + 1 .. #Vects] do
        // Take the kernel of the first rank+1 surviving vectors, which must have at least a
        // one-dimensional kernel. Pick any element k of the kernel. So k is a linear combination
        // of length rank+1, such that sum(k[i] * Vects[X[i]]) = 0.
        ker := NullSpace(Matrix(Vects[X[1..rank+1]]));
        k := Basis(ker)[1];

        // Let v be the smallest p-valuation of any entry of k. If k[i] is an entry with this
        // smallest valuation, then k[i] Vects[X[i]] = -sum(k[j] Vects[X[j]], j =/= i), and
        // scaling the whole linear combination by p^(-v) makes the term on the left invertible, so
        // we have that Vects[X[i]] is a Z_(p)-linear combination of the others.
        // There may be multiple i that work: use the maximum.
        //
        // Joel: I added coercions into rationals, to deal with the general parabolic case. I don't think
        //       this is actually correct in general (what if an element of k ends up having a polynomial
        //       generator in it?), but this doesn't seem to come up in small cases.
        if p ne 0 and Characteristic(BaseRing(Vects[1])) eq 0 then
            v := Minimum([Valuation(Rationals()!i, p) : i in Eltseq(k)]);
            j := Maximum([ i : i in [1..rank+1] | Valuation(Rationals()!k[i], p) eq v]);
            Remove(~X, j); // Removes the element at index j, i.e. discards Vects[X[j]].
        else
            j := Maximum([ i : i in [1..rank+1] | k[i] ne 0 ]);
            Remove(~X, j);
        end if;
    end for;

    return X;
end intrinsic;

intrinsic GradedRank(R::Rng, homs::SeqEnum[StdMor]) -> RngElt
{Return the graded rank of the hom space, where grade 1 corresponds to the generator R.1.}
    return &+[R.1^(f`deg) : f in homs];
end intrinsic;

intrinsic GetCharacter(B::BSCat, homCollection::Assoc, ASMod::FModIHke) -> EltIHke
{Return the character of the collection of hom spaces.}
    elts := Setseq(Keys(homCollection));
    coeffs := [GradedRank(BaseRing(ASMod), homCollection[w]) : w in elts];
    H := StandardBasis(ASMod);
    v := BaseRing(ASMod).1;
    return &+[H.elts[i] * coeffs[i] : i in [1..#elts]];
end intrinsic;

intrinsic MaximumNumeratorOrDenominator(indec::QPDI) -> RngIntElt
{Extract the maximum numerator or denominator seen, across all the hom spaces in this indecomposable.}
    max := Maximum([MaximumNumeratorOrDenominator(homs) : homs in [indec`homsIn, indec`homsOut]]);
    return max;
end intrinsic;

intrinsic MaximumNumeratorOrDenominator(homs::Assoc) -> RngIntElt
{Extract the maximum numerator or denominator seen, across all the hom spaces.}
    max := Maximum([MaximumNumeratorOrDenominator(f`mat) : f in &cat[fs : fs in homs]]);
    return max;
end intrinsic;

intrinsic MaximumNumeratorOrDenominator(mat::MtrxSprs) -> RntIntElt
{Extract the maximum numerator or denominator in the matrix.}
    rationals := [0] cat [triple[3] : triple in Eltseq(mat)];
    biggest := Maximum([
        Max(AbsoluteValue(Numerator(r)), AbsoluteValue(Denominator(r)))
        : r in rationals
    ]);
    return biggest;
end intrinsic;
