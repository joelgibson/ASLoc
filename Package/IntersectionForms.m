intrinsic LocalIntersectionForm(B::BSCat, bsword::SeqEnum[RngIntElt], w::GrpFPCoxElt, deg::RngIntElt : I := []) -> AlgMatElt
{A graded piece of the local intersection form of a Bott-Samelson bsword, calculated at the element w <= bsword. The
 triple (M, outexps, inexps) is returned, where M is an |outexps| x |inexps| matrix over the integers, outexps are the
 degree deg subexpressions evaluating to w, and inexps are the degree (-deg) subexpressions evaluating to w.
 If I is passed, then only the I-antispherical subexpressions are used.}
    W := B`W;
    require forall(s){s : s in bsword | 1 le s and s le Rank(W)}:
        "The Bott-Samelson generator", s, "does not belong to the group", W;

    if #I gt 0 then
        require I subset [1..Rank(W)]: "The parabolic generators", I, "are out of range.";
        require IsMinimal(I, W ! bsword): "The word", bsword, "is not antispherical with respect to", I;
        require IsMinimal(I, w): "The element", w, "is not antispherical with respect to", I;
        subexps := ASSubexpressionsEvaluatingTo(W, I, bsword, w);
    else
        vprintf ASLoc, 2: "Calculating subexpressions of %o evaluating to %o ... ", bsword, Eltseq(w);
        vtime ASLoc, 2: subexps := SubexpressionsEvaluatingTo(W, bsword, w);
    end if;

    inexps := [subexp : subexp in subexps | DeodharDefect(W, bsword, subexp) eq -deg];
    outexps := [subexp : subexp in subexps | DeodharDefect(W, bsword, subexp) eq deg];
    vprintf ASLoc, 2: "Have %o light leaves in and %o light leaves out to build.\n", #inexps, #outexps;

    // What would be nice to do here is to directly build two lists: the images of the light leaves in and out,
    // then directly calculate the pairing. Unfortunately (for E6 in characteristic 2 for instance) there are some
    // intersection forms requiring something like a 2500 x 2500 matrix, and doing this in this way wastes far too
    // much memory since it all builds up in these lists.
    //
    // We should be able to get rid of a lot of the memory usage by calculating a light leaf, recording it as a vector
    // in a matrix, and then discarding the leaf itself. Our light leaf in this context is not really a light leaf, it's
    // more like a sparsely represented last column of a localised light leaf matrix: a map from 01-sequences to rational
    // functions. We'll keep inserting these 01-sequences into a growing indexed set so we can replace them by numbers,
    // then furthermore we evaluate the rational functions at (1, ..., 1) and stick them in the sparse matrix.
    //
    // Keep two sparse matrices, one for the light leaves in and one for the light leaves out, with their inner dimensions
    // agreeing (and indexed by that set). Then the local intersection form is their product.
    seqToIndex := {@ @};
    QQ := Rationals();
    spec := hom<B`FR -> QQ | [QQ!1 : i in [1..Rank(B`W)]]>;

    inMat := SparseMatrix(QQ);
    vprintf ASLoc, 2: "Building %o light leaves in... ", #inexps;
    vtime ASLoc, 2: for i -> subexp in inexps do
        // Append(~llsin, LocalisedLLUp(B, bsword, subexp));
        ll := ApplyLightLeafIn(B, [], bsword, subexp, [1 : _ in [1..#w]]);
        assert ll`bsseq eq bsword;
        for k -> coeff in ll`terms do
            Include(~seqToIndex, k);
            SetEntry(~inMat, Index(seqToIndex, k), i, spec(coeff));
        end for;
    end for;

    outMat := SparseMatrix(QQ);
    vprintf ASLoc, 2: "Building %o light leaves out... ", #outexps;
    vtime ASLoc, 2: for i -> subexp in outexps do
        //Append(~llsout, LocalisedLLDown(B, bsword, subexp));
        ll := ApplyLightLeafOut(B, [], bsword, subexp, [1 : _ in [1..#w]]);
        assert ll`bsseq eq bsword;
        for k -> coeff in ll`terms do
            Include(~seqToIndex, k);
            SetEntry(~outMat, i, Index(seqToIndex, k), spec(coeff));
        end for;
    end for;

    // We may have to now enlarge the inner dimensions of the matrices. If they are not the right shape, add a zero in
    // the (currently empty, and out of the matrix) corner.
    if Nrows(inMat) lt #seqToIndex then
        // Bug in Magma as of Magma V2.26-9: we need to extend with a 1 first and then set it to zero, otherwise the row
        // dimension does not get enlarged. As of V2.26-10 this is meant to be fixed, but if I remove the following line
        // I get random segfaults...
        SetEntry(~inMat, #seqToIndex, #inexps, 1);

        SetEntry(~inMat, #seqToIndex, #inexps, 0);
    end if;
    if Ncols(outMat) lt #seqToIndex then
        SetEntry(~outMat, #outexps, #seqToIndex, 0);
    end if;
    assert Nrows(inMat) eq Ncols(outMat);

    return ChangeRing(outMat * inMat, Integers()), outexps, inexps;
end intrinsic;

// Testing pairwise on the first 200 elements of C4, this naive recursion slightly outperforms the existing
// method in Hecke/Expressions.m, and of course greatly outperforms the naive 2^n soluion.
// It could be rewritten iteratively to be even faster.
intrinsic SubexpressionsEvaluatingTo(W::GrpFPCox, bsword::SeqEnum, x::GrpFPCoxElt) -> SeqEnum[SeqEnum[RngIntElt]]
{Return all subexpressions (01-sequences) of bsword evaluating to x.}
    // Let S([s1, ..., sn], x) be the set of subexpressions of [s1, ..., sn] evaluating to x.
    // If l(x) > n, then S([s1, ..., sn], x) = empty
    // If l(x) = n, then S([s1, ..., sn], x) = {111111} if s1*...*sn = x, and empty otherwise.
    // Recursive case:   S([s1, ..., sn], x) = S([s1, ..., sn-1], x * sn).1 union S([s1, ..., sn-1], sn).0,
    //   where . means concatenation.
    if #x gt #bsword then
        return [];
    elif #x eq #bsword then
        return x eq W ! bsword select [[1 : _ in bsword]] else [];
    else return
        [exp cat [1] : exp in SubexpressionsEvaluatingTo(W, bsword[1..#bsword-1], x * W.bsword[#bsword])]
        cat
        [exp cat [0] : exp in SubexpressionsEvaluatingTo(W, bsword[1..#bsword-1], x)];
    end if;
end intrinsic;

intrinsic IsAntisphericalSubexpression(W::GrpFPCox, I::[RngIntElt], word::[RngIntElt], exp::[RngIntElt]) -> BoolElt
{Predicate testing whether exp is an I-antispherical subexpression of word.}
    require I subset [1..Rank(W)]: "The parabolic generating set", I, "is out of range";
    require word subset [1..Rank(W)]: "The word", word, "is not in the generators of W";
    require exp subset [0, 1]: "The expression", exp, "should have only zeros and ones";
    require #word eq #exp: "The word and expression have different lengths.";

    x := W.0;
    for i := 1 to #word do
        if not IsMinimal(I, x * W.word[i]) then
            return false;
        end if;

        x := x * W.word[i]^exp[i];
    end for;

    return true;
end intrinsic;

intrinsic ASSubexpressionsEvaluatingTo(W::GrpFPCox, I::[RngIntElt], bsword::[RngIntElt], x::GrpFPCoxElt) -> SeqEnum[SeqEnum[RngIntElt]]
{Return all of the I-antispherical subexpressions (01-sequences) of bsword evaluating to x.}
    return ASSubexpressionsEvaluatingTo(W, I, bsword, W.0, x);
end intrinsic;

intrinsic ASSubexpressionsEvaluatingTo(W::GrpFPCox, I::[RngIntElt], bsword::[RngIntElt], x::GrpFPCoxElt, y::GrpFPCoxElt) -> SeqEnum[SeqEnum[RngIntElt]]
{Recursive helper: return all of the subexpressions e of bsword such that x . bsword^e = y, all the subexpressions are I-antispherical.}
    require IsMinimal(I, x): x, "is not minimal in its right", I, "coset";

    // Base case: if the word is empty, no antispherical condition to check.
    if #bsword eq 0 then
        return x eq y select [[]] else [];
    end if;

    // If there are not enough letters to have a hope of reaching y, then early exit.
    if #y gt #x + #bsword then
        return [];
    end if;

    // Otherwise, the first letter needs to pass the antispherical condition.
    if #bsword gt 0 and not IsMinimal(I, x * W.bsword[1]) then
        return [];
    end if;

    // If l(y) = l(x) + l(bsword) then there is only one way of reaching y: by taking a 1 every time.
    // Early-terminate in this case, checking if the resulting expression would be antispherical at
    // every point.
    if #y eq #x + #bsword then
        if x * (W ! bsword) ne y then
            return [];
        end if;

        for s in bsword do
            if not IsMinimal(I, x * W.s) then
                return [];
            end if;
            x := x * W.s;
        end for;

        return [[1 : _ in bsword]];
    end if;

    // Recursive case: we can place either a 0 or a 1 in this position.
    return
        [[0] cat exp : exp in ASSubexpressionsEvaluatingTo(W, I, bsword[2 .. #bsword], x, y)]
        cat
        [[1] cat exp : exp in ASSubexpressionsEvaluatingTo(W, I, bsword[2 .. #bsword], x * W.bsword[1], y)];
end intrinsic;

intrinsic DeodharDefect(W::GrpFPCox, word::[RngIntElt], subexp::[RngIntElt]) -> RngIntElt
{Measure the Deodhar defect (#U0 - #D0) of a subexpression.}
    require #word eq #subexp: "Word and subexpression have different lengths";

    defect := 0;
    w := W.0;
    for i in [1..#word] do
        if subexp[i] eq 0 then
            defect +:= #(w * W.word[i]) gt #w select 1 else -1;
        end if;
        w *:= (W.word[i])^subexp[i];
    end for;

    return defect;
end intrinsic;

intrinsic DecorateSubexpression(W::GrpFPCox, word::[RngIntElt], subexp::[RngIntElt]) -> SeqEnum[Tup]
{Return a sequence of <"U", 0>, <"D", 1>, etc.}
    require #word eq #subexp: "Word and subexpression have different lengths";

    w := W.0;
    decorations := [];
    for i in [1..#word] do
        Append(~decorations, <#(w * W.word[i]) gt #w select "U" else "D", subexp[i]>);
        w *:= (W.word[i])^subexp[i];
    end for;

    return decorations;
end intrinsic;


function makeBraidUp(B, W, bsseq, s)
    ending, moves := BraidToEndWith(W, bsseq, s);
    // printf "Braid moves from %o to %o: %o\n", bsseq, ending, moves;
    braid := BSId(B, bsseq);
    for move in moves do
        braid := BraidUp(B, braid`bscod, move[1], move[2]) * braid;
    end for;
    return braid;
end function;

function makeTopEndWith(B, W, mor, s)
    if mor`bscod[#mor`bscod] ne s then
        time
        return makeBraidUp(B, W, mor`bscod, s) * mor;
    end if;
    return mor;
end function;

declare type BSStdMor;
declare attributes BSStdMor:
    bsseq,  // The Bott-Samelson sequence
    terms;  // An associative array {01-sequence => coefficient}.

intrinsic Print(mor::BSStdMor)
{}
    printf "StdMor(%o, %o)", mor`bsseq, [<k, v> : k -> v in mor`terms];
end intrinsic;

function BSStdMorConstruct(bsseq, terms)
    assert Type(bsseq) eq SeqEnum;
    assert Type(terms) eq Assoc;
    assert forall{k : k -> _ in terms | #k eq #bsseq};
    mor := New(BSStdMor);
    mor`bsseq := bsseq;
    mor`terms := terms;
    return mor;
end function;

function BSStdMorConstruct(bsseq, terms)
    error if not forall{k : k -> _ in terms | #k eq #bsseq},
        Sprintf("Word is %o, incompatible with keys %o", bsseq, Keys(terms));
    mor := New(BSStdMor);
    mor`bsseq := bsseq;
    mor`terms := terms;
    return mor;
end function;

intrinsic BSStdMorId(B::BSCat) -> BSStdMor
{}
    terms := AssociativeArray();
    terms[[Integers() |]] := Rationals() ! 1;
    return BSStdMorConstruct([Integers() |], terms);
end intrinsic;

intrinsic BSStdMorComponent(B::BSCat, word::[RngIntElt], subseq::[RngIntElt]) -> BSStdMor
{}
    terms := AssociativeArray();
    terms[subseq] := Rationals() ! 1;
    return BSStdMorConstruct(word, terms);
end intrinsic;

// Convert a 01-sequence to and from its index in the list 000, 001, 010, 011, 100, ...
// The Magma Seqint and Intseq functions which convert between numbers and lists of digits
// in a given base consider the least significant digit to be first, rather than last.
exp2idx := func<exp | Seqint(Reverse(exp), 2) + 1>;
function idx2exp(idx, seqlen)
    error if not (1 le idx and idx le 2^seqlen),
        idx, "is not a valid index for a 01-sequence of length", seqlen;
    seq := [Integers() | 0 : _ in [1 .. seqlen]];
    for i -> e in Intseq(idx - 1, 2) do
        seq[seqlen - i + 1] := e;
    end for;
    return seq;
end function;

intrinsic BSStdMorApply(B::BSCat, id1::[RngIntElt], bsmor::BSMor, id2::[RngIntElt], mor::BSStdMor) -> BSStdMor
{Caculate the image (id1 ⊗ bsmor ⊗ id3) o (mor), where mor is a localised thingo.}
    require (id1 cat bsmor`bsdom cat id2) eq mor`bsseq:
        Sprintf("Morphism word is %o, but (id, f, id) domain is (%o, %o, %o)", mor`bsseq, id1, bsmor`bsdom, id2);

    W := B`W;
    QQ := Rationals();
    spec := hom<B`FR -> QQ | [QQ!1 : i in [1..Rank(B`W)]]>;
    newTerms := AssociativeArray();

    for subexp -> coeff in mor`terms do
        twist := FActionByElt(B, W ! [s : i -> s in id1 | subexp[i] eq 1]);
        subexpidx := exp2idx(subexp[#id1 + 1 .. #id1 + #bsmor`bsdom]);
        mat := bsmor`stdmor`mat;
        for j in Support(mat, subexpidx) do
            newexp := subexp[1 .. #id1] cat idx2exp(j, #bsmor`bscod) cat subexp[#subexp - #id2 + 1 .. #subexp];
            newTerms[newexp] := IsDefined(newTerms, newexp)
                select newTerms[newexp] + coeff * spec(twist(mat[subexpidx, j]))
                  else coeff * spec(twist(mat[subexpidx, j]));
        end for;
    end for;

    return BSStdMorConstruct(id1 cat bsmor`bscod cat id2, newTerms);
end intrinsic;

intrinsic BSStdMorApply(B::BSCat, mor::BSStdMor, id1::[RngIntElt], bsmor::BSMor, id2::[RngIntElt]) -> BSStdMor
{Caculate the image (mor) o (id1 ⊗ bsmor ⊗ id3), where mor is a localised thingo.}
    require (id1 cat bsmor`bscod cat id2) eq mor`bsseq:
        Sprintf("Morphism word is %o, but (id, f, id) codomain is (%o, %o, %o)", mor`bsseq, id1, bsmor`bscod, id2);

    W := B`W;
    QQ := Rationals();
    spec := hom<B`FR -> QQ | [QQ!1 : i in [1..Rank(B`W)]]>;
    newTerms := AssociativeArray();

    for subexp -> coeff in mor`terms do
        twist := FActionByElt(B, W ! [s : i -> s in id1 | subexp[i] eq 1]);
        subexpidx := exp2idx(subexp[#id1 + 1 .. #id1 + #bsmor`bscod]);
        mat := Transpose(bsmor`stdmor`mat);
        for j in Support(mat, subexpidx) do
            newexp := subexp[1 .. #id1] cat idx2exp(j, #bsmor`bsdom) cat subexp[#subexp - #id2 + 1 .. #subexp];
            newTerms[newexp] := IsDefined(newTerms, newexp)
                select newTerms[newexp] + coeff * spec(twist(mat[subexpidx, j]))
                  else coeff * spec(twist(mat[subexpidx, j]));
        end for;
    end for;

    return BSStdMorConstruct(id1 cat bsmor`bsdom cat id2, newTerms);
end intrinsic;

intrinsic 'cat'(mor::BSStdMor, word::[RngIntElt]) -> BSStdMor
{Tensor on the right, extending subexpressions by 1's.}
    newTerms := AssociativeArray();
    ones := [1 : _ in [1 .. #word]];
    for k -> v in mor`terms do
        newTerms[k cat ones] := v;
    end for;
    return BSStdMorConstruct(mor`bsseq cat word, newTerms);
end intrinsic;

intrinsic TopStdLLDown(B::BSCat, bsword::SeqEnum[RngIntElt], subexp::SeqEnum[RngIntElt]) -> BSStdMor
{A light leaf for BS(bsword) down to bsword^subexp, evaluated only at the top element of bsword^subexp: the all 1's sequence.}
    require #bsword eq #subexp: "Length", #bsword, "of bsword must agree with length", #subexp, "of 0-1 sequence.";
    require forall{s : s in subexp | s eq 0 or s eq 1}: "Subexp must be a 0-1 sequence.";

    // w will be the element that the subexpression evaluates to so far, starting at the identity.
    W := B`W;
    w := W.0;
    leaf := BSId(B, []);

    // The stdmor will be the image of the stdmor we are building, starting with the identity.
    std := BSStdMorId(B);

    for i := 1 to #bsword do
        si := bsword[i];
        ei := subexp[i];
        if #(w * W.si) gt #w then
            // print "U", ei;
            leaf := ei eq 0
                select leaf cat Counit(B, si)   // U0
                  else leaf cat [si];           // U1
            std := ei eq 0
                select BSStdMorApply(B, std`bsseq, Counit(B, si), [], std cat [si])
                  else std cat [si];
        else
            // print "D", ei;
            // D0 or D1. We might need to apply some braid moves.
            _, moves := BraidToEndWith(W, std`bsseq, si);
            for move in moves do
                std := BSStdMorApply(B, std`bsseq[1..move[1]-1], Braid(B, std`bsseq[move[1]], std`bsseq[move[1] + 1]), std`bsseq[move[2] + 1 .. #std`bsseq], std);
            end for;
            // braid := BSId(B, leaf`bscod);
            // for move in moves do
            //     braid := BraidUp(B, braid`bscod, move[1], move[2]) * braid;
            // end for;
            leaf := makeTopEndWith(B, W, leaf, si);
            if leaf`bscod[#leaf`bscod] ne si then
                leaf := makeBraidUp(B, W, leaf`bscod, si) * leaf;
            end if;

            if ei eq 0 then // D0
                leaf := &*[
                    leaf`bscod[1..#leaf`bscod-1] cat Mult(B, si),
                    leaf cat [si]
                ];
            else
                leaf := &*[
                    leaf`bscod[1..#leaf`bscod-1] cat Cap(B, si),
                    leaf cat [si]
                ];
            end if;

            std := ei eq 0
                select BSStdMorApply(B, std`bsseq[1 .. #std`bsseq - 1], Mult(B, si), [], std cat [si])
                  else BSStdMorApply(B, std`bsseq[1 .. #std`bsseq - 1], Cap(B, si), [], std cat [si]);

        end if;

        // print Transpose(Matrix(LimitDomain(leaf`stdmor, #Domain(leaf`stdmor))));
        // print [<k, v> : k -> v in std`terms];

        leafterms := {coeff : coeff in Eltseq(Transpose(Matrix(LimitCodomain(leaf`stdmor, #Codomain(leaf`stdmor)))))} diff {0};
        stdterms := {v : k -> v in std`terms};
        print "Light leaf is", Matrix(leaf`stdmor);
        print "Last col of light leaf is", Transpose(Matrix(LimitCodomain(leaf`stdmor, #Codomain(leaf`stdmor))));
        print "Std is", std;
        print "Leafterms:", leafterms;
        print "Stdterms:", stdterms;
        error if leafterms ne stdterms,
            "Leafterms is", leafterms,
            "stdterms is", stdterms;
        w := w * (W.si)^ei;
    end for;

    return std;
end intrinsic;

intrinsic ApplyLightLeafOut(B::BSCat, left::[RngIntElt], right::[RngIntElt], rightexp::[RngIntElt], seq::[RngIntElt]) -> BSStdMor
{The light leaf for bsword -> bsword^subexp, evaluated by putting a standard idempotent on top. This function is
 recursive, to start it off we should have left = [].
 Left is a reduced expression.}
    if #right eq 0 then
        return BSStdMorComponent(B, left, seq);
    end if;

    W := B`W;
    w := W ! left;
    assert #w eq #left;

    // Up
    if #(w * W.right[1]) gt #w then
        newLeft := rightexp[1] eq 1 select left cat [right[1]] else left;
        above := ApplyLightLeafOut(B, newLeft, right[2..#right], rightexp[2..#rightexp], seq);
        return rightexp[1] eq 0
            select BSStdMorApply(B, above, left, Counit(B, right[1]), right[2..#right]) // U0
              else above;                                                               // U1
    end if;

    // Down
    endBraid, moves := BraidToEndWith(W, left, right[1]);
    // printf "!!!Applying braid moves %o -> %o: %o\n", left, endBraid, moves;
    newLeft := rightexp[1] eq 1 select endBraid[1..#endBraid - 1] else endBraid;
    above := ApplyLightLeafOut(B, newLeft, right[2..#right], rightexp[2..#rightexp], seq);
    assert above`bsseq[1..#newLeft] eq newLeft;

    above := rightexp[1] eq 0
        select BSStdMorApply(B, above, newLeft[1..#left-1], Mult(B, right[1]), right[2..#right])
          else BSStdMorApply(B, above, newLeft[1..#left-1], Cap(B, right[1]), right[2..#right]);

    for move in Reverse(moves) do
        braid := Braid(B, above`bsseq[move[1]+1], above`bsseq[move[1]]);
        above := BSStdMorApply(B, above, above`bsseq[1..move[1]-1], braid, above`bsseq[move[2]+1..#above`bsseq]);
    end for;
    // print "Applied braid", moves;
    assert above`bsseq[1..#left] eq left;
    return above;
end intrinsic;

intrinsic ApplyLightLeafIn(B::BSCat, left::[RngIntElt], right::[RngIntElt], rightexp::[RngIntElt], seq::[RngIntElt]) -> BSStdMor
{The light leaf for bsword <- bsword^subexp, evaluated by putting a standard idempotent on top. This function is
 recursive, to start it off we should have left = [].
 Left is a reduced expression.}
    if #right eq 0 then
        return BSStdMorComponent(B, left, seq);
    end if;

    W := B`W;
    w := W ! left;
    assert #w eq #left;

    // Up
    if #(w * W.right[1]) gt #w then
        newLeft := rightexp[1] eq 1 select left cat [right[1]] else left;
        below := ApplyLightLeafIn(B, newLeft, right[2..#right], rightexp[2..#rightexp], seq);
        return rightexp[1] eq 0
            select BSStdMorApply(B, left, Unit(B, right[1]), right[2..#right], below) // U0
              else below;                                                             // U1
    end if;

    // Down
    endBraid, moves := BraidToEndWith(W, left, right[1]);
    // printf "!!!Applying braid moves %o -> %o: %o\n", left, endBraid, moves;
    newLeft := rightexp[1] eq 1 select endBraid[1..#endBraid - 1] else endBraid;
    below := ApplyLightLeafIn(B, newLeft, right[2..#right], rightexp[2..#rightexp], seq);
    assert below`bsseq[1..#newLeft] eq newLeft;

    below := rightexp[1] eq 0
        select BSStdMorApply(B, newLeft[1..#left-1], Comult(B, right[1]), right[2..#right], below)
          else BSStdMorApply(B, newLeft[1..#left-1], Cup(B, right[1]), right[2..#right], below);

    for move in Reverse(moves) do
        braid := Braid(B, below`bsseq[move[1]], below`bsseq[move[1]+1]);
        below := BSStdMorApply(B, below`bsseq[1..move[1]-1], braid, below`bsseq[move[2]+1..#below`bsseq], below);
    end for;
    // print "Applied braid", moves;
    assert below`bsseq[1..#left] eq left;
    return below;
end intrinsic;


intrinsic TopStdLLUp(B::BSCat, bsword::SeqEnum[RngIntElt], subexp::SeqEnum[RngIntElt]) -> BSStdMor
{A light leaf for bsword^subexp up to BS(bsword), evaluated only at the top element of bsword^subexp: the all 1's sequence.
}
    require #bsword eq #subexp: "Length", #bsword, "of bsword must agree with length", #subexp, "of 0-1 sequence.";
    require forall{s : s in subexp | s eq 0 or s eq 1}: "Subexp must be a 0-1 sequence.";

    // w will be the element that the subexpression evaluates to so far.
    // leaf will be the localised light leaf we are building. Both start as the identity.
    W := B`W;
    w := W.0;
    leaf := BSId(B, []);
    std := BSStdMorId(B);

    for i := 1 to #bsword do
        si := bsword[i];
        ei := subexp[i];
        if #(w * W.si) gt #w then
            leaf := ei eq 0
                select leaf cat Unit(B, si)     // U0
                  else leaf cat [si];           // U1
            std := ei eq 0
                select BSStdMorApply(B, std cat [si], std`bsseq, Unit(B, si), [])
                  else std cat [si];
        else
            // D0 or D1. We might need to apply some braid moves.
            _, moves := BraidToEndWith(W, leaf`bsdom, si);
            braid := BSId(B, leaf`bsdom);
            for move in moves do
                braid := braid * BraidDown(B, braid`bsdom, move[1], move[2]);
            end for;
            leaf := leaf * braid;

            for move in moves do
                std := BSStdMorApply(B, std, std`bsseq[1..move[1]-1], Braid(B, std`bsseq[move[1] + 1], std`bsseq[move[1]]), std`bsseq[move[2] + 1 .. #std`bsseq]);
            end for;

            std := ei eq 0
                select BSStdMorApply(B, std cat [si], std`bsseq[1 .. #std`bsseq - 1], Comult(B, si), [])
                  else BSStdMorApply(B, std cat [si], std`bsseq[1 .. #std`bsseq - 1], Cup(B, si), []);


            if ei eq 0 then // D0
                leaf := &*[
                    leaf cat [si],
                    leaf`bsdom[1..#leaf`bsdom-1] cat Comult(B, si)
                ];
            else
                leaf := &*[
                    leaf cat [si],
                    leaf`bsdom[1..#leaf`bsdom-1] cat Cup(B, si)
                ];
            end if;
        end if;

        w := w * (W.si)^ei;
    end for;

    return std;
end intrinsic;



intrinsic LocalisedLLDown(B::BSCat, bsword::SeqEnum[RngIntElt], subexp::SeqEnum[RngIntElt]) -> StdMor
{Returns the light-leaf from the Bott-Samelson object B(bsword) down to the subexpression bsword^subexp,
 as a localised matrix in the standard category.
 TODO: Really need to rename BSCat and StdCat.
}
    require #bsword eq #subexp: "Length", #bsword, "of bsword must agree with length", #subexp, "of 0-1 sequence.";
    require forall{s : s in subexp | s eq 0 or s eq 1}: "Subexp must be a 0-1 sequence.";

    // w will be the element that the subexpression evaluates to so far.
    // leaf will be the localised light leaf we are building. Both start as the identity.
    W := B`W;
    w := W.0;
    leaf := BSId(B, []);

    for i := 1 to #bsword do
        si := bsword[i];
        ei := subexp[i];
        if #(w * W.si) gt #w then
            leaf := ei eq 0
                select leaf cat Counit(B, si)   // U0
                  else leaf cat [si];           // U1
        else
            // D0 or D1. We might need to apply some braid moves.
            // _, moves := BraidToEndWith(W, leaf`bscod, si);
            // braid := BSId(B, leaf`bscod);
            // for move in moves do
            //     braid := BraidUp(B, braid`bscod, move[1], move[2]) * braid;
            // end for;
            leaf := makeTopEndWith(B, W, leaf, si);
            // if leaf`bscod[#leaf`bscod] ne si then
            //     leaf := makeBraidUp(B, W, leaf`bscod, si) * leaf;
            // end if;

            if ei eq 0 then // D0
                leaf := &*[
                    leaf`bscod[1..#leaf`bscod-1] cat Mult(B, si),
                    leaf cat [si]
                ];
            else
                leaf := &*[
                    leaf`bscod[1..#leaf`bscod-1] cat Cap(B, si),
                    leaf cat [si]
                ];
            end if;
        end if;

        w := w * (W.si)^ei;
    end for;

    return leaf`stdmor;
end intrinsic;

intrinsic LocalisedLLUp(B::BSCat, bsword::SeqEnum[RngIntElt], subexp::SeqEnum[RngIntElt]) -> StdMor
{Returns the light-leaf to the Bott-Samelson object B(bsword) up from the subexpression bsword^subexp,
 as a localised matrix in the standard category.
 TODO: Really need to rename BSCat and StdCat.
}
    require #bsword eq #subexp: "Length", #bsword, "of bsword must agree with length", #subexp, "of 0-1 sequence.";
    require forall{s : s in subexp | s eq 0 or s eq 1}: "Subexp must be a 0-1 sequence.";

    // w will be the element that the subexpression evaluates to so far.
    // leaf will be the localised light leaf we are building. Both start as the identity.
    W := B`W;
    w := W.0;
    leaf := BSId(B, []);

    for i := 1 to #bsword do
        si := bsword[i];
        ei := subexp[i];
        if #(w * W.si) gt #w then
            leaf := ei eq 0
                select leaf cat Unit(B, si)     // U0
                  else leaf cat [si];           // U1
        else
            // D0 or D1. We might need to apply some braid moves.
            _, moves := BraidToEndWith(W, leaf`bsdom, si);
            braid := BSId(B, leaf`bsdom);
            for move in moves do
                braid := braid * BraidDown(B, braid`bsdom, move[1], move[2]);
            end for;
            leaf := leaf * braid;

            if ei eq 0 then // D0
                leaf := &*[
                    leaf cat [si],
                    leaf`bsdom[1..#leaf`bsdom-1] cat Comult(B, si)
                ];
            else
                leaf := &*[
                    leaf cat [si],
                    leaf`bsdom[1..#leaf`bsdom-1] cat Cup(B, si)
                ];
            end if;
        end if;

        w := w * (W.si)^ei;
    end for;

    return leaf`stdmor;
end intrinsic;


// A different strategy for finding braid moves. Seems to perform on-par with the current strategy, at least
// in F4 p=2 tests, so leaving it out for now.
intrinsic NewBraidToEndWith(W::GrpFPCox, word::[RngIntElt], t::RngIntElt) -> SeqEnum[RngIntElt], SeqEnum[Tup]
{Another strategy for finding braid moves to apply to word to make it end with t.}
    require #word ne 0: "Cannot braid an empty word.";
    require forall(s){s : s in word | 1 le s and s le Rank(W)}:
        "The letter", s, "in the word", word, "is not a generator of the Coxeter group", W;
    require 1 le t and t le Rank(W):
        "The letter", t, "is not a generator of the Coxeter group", W;

    w := W ! word;
    require #word eq #w: "The word", word, "is not reduced.";
    require w*W.t lt w: "The letter", t, "is not a right descent of the word", word;

    // Since t is a right descent, word . t is not reduced, hence by the deletion condition there is a unique
    // index i of word that can be deleted to make it reduced again. This index can be found by looking at the
    // "suffix conjugates" word[i] ^ (word[i+1 .. #word]), and looking for which one is equal to t.
    error if not exists(i){i : i in [1 .. #word] | W.word[i] ^ (W ! word[i+1 .. #word]) eq W.t},
        "Could not find a deletion index";

    // If the deletion index is #word then word[#word] = t, so we are done.
    if i eq #word then
        return word, [];
    end if;

    // Start applying braid moves to the suffix in a breadth-first search, looking for a sequence of braid moves
    // which raises the deletion index. During this search we will keep track of the words we have seen in an
    // associative array which maps them to the braid sequences leading to them.
    M := CoxeterMatrix(W);
    seen := AssociativeArray();
    seen[word] := [];
    frontier := {word};

    repeat
        newFrontier := {};
        for word in frontier do
            for j := #word-1 to i by -1 do
                m := M[word[j], word[j+1]];
                if m eq 0 or m eq 1 then
                    continue;
                end if;
                if j + m - 1 le #word and forall{k : k in [j .. j + m - 1] | word[k] eq ((k - j) mod 2 eq 0 select word[j] else word[j+1])} then
                    // Apply the braid move
                    newWord := word;
                    for k := j to j + m - 1 do
                        newWord[k] := (k - j) mod 2 eq 0 select word[j+1] else word[j];
                    end for;
                    assert W ! word eq W ! newWord;

                    if IsDefined(seen, newWord) then
                        continue;
                    end if;

                    // Construct a new deletion index.
                    error if not exists(l){i : i in [1 .. #word] | W.newWord[i] ^ (W ! newWord[i+1 .. #word]) eq W.t},
                        "Could not find a deletion index";

                    if l gt i then
                        finalWord, braids := NewBraidToEndWith(W, newWord, t);
                        return finalWord, seen[word] cat [<j, j + m - 1>] cat braids;
                    end if;

                    seen[newWord] := seen[word] cat [<j, j + m - 1>];
                    Include(~newFrontier, newWord);
                end if;
            end for;
        end for;

        frontier := newFrontier;
    until #frontier eq 0;

    error "Could not find any reduced words ending in t.";
end intrinsic;


intrinsic BraidToEndWith(W::GrpFPCox, word::[RngIntElt], t::RngIntElt) -> SeqEnum[RngIntElt], SeqEnum[Tup]
{For a reduced word in a Coxeter group and a right descent t, return another reduced word for the
 same element ending in t, and a sequence of braid moves that can be applied to the original word
 to get there. (This is possible if and only if t is a right descent of word).

 The braid moves are returned as a sequence of tuples, where each tuple is a pair <i, j> with i < j.
 For instance, the returned sequence [<2, 4>, <3, 6>] would mean to apply an m_st=3 braid to indices
 [2,3,4], followed by an m_st=4 braid to indices [3,4,5,6].}
    require #word ne 0: "Cannot braid an empty word.";
    require forall(s){s : s in word | 1 le s and s le Rank(W)}:
        "The letter", s, "in the word", word, "is not a generator of the Coxeter group", W;
    require 1 le t and t le Rank(W):
        "The letter", t, "is not a generator of the Coxeter group", W;

    w := W ! word;
    require #word eq #w: "The word", word, "is not reduced.";
    require w*W.t lt w: "The letter", t, "is not a right descent of the word", word;

    // Let s be the last letter of the word. If s = t, then we are done.
    s := word[#word];
    if s eq t then
        return word, [];
    end if;

    // Since both s and t are right descents, there exists a reduced expression ending [...ts].
    // Once we have this reduced expression, we can apply a braid move to change it to [...st].
    // In order to get such a reduced expression, we recursively solve a subproblem on the word
    // with the last letter chopped off.
    mst := Order(W.s * W.t);
    braidedWord := word;
    braidLocations := [];
    for i in [2..mst] do
        endLetter := i mod 2 eq 0 select t else s;
        newWord, braids := BraidToEndWith(W, braidedWord[1..#braidedWord - i + 1], endLetter);
        braidedWord := newWord cat braidedWord[#braidedWord - i + 2 .. #braidedWord];
        braidLocations cat:= braids;
    end for;

    // Now the word should end [...ts].
    oldEnd := Reverse([i mod 2 eq 1 select s else t : i in [1..mst]]);
    newEnd := Reverse([i mod 2 eq 1 select t else s : i in [1..mst]]);
    assert braidedWord[#braidedWord - mst + 1 .. #braidedWord] eq oldEnd;
    braidedWord := braidedWord[1..#braidedWord - mst] cat newEnd;
    Append(~braidLocations, <#braidedWord - mst + 1, #braidedWord>);

    return braidedWord, braidLocations;
end intrinsic;

intrinsic RightStar(W::GrpFPCox, w::GrpFPCoxElt, s::RngIntElt, t::RngIntElt) -> GrpFPCoxElt, BoolElt
{Apply the right <s, t>-star operation to w, returning w*. Here we define the right star
 operation to fix the minimal and maximal coset representatives pointwise, but if w is
 minimal or maximal then the second argument returned is false.}
    // First deal with the minimal or maximal case.
    size := #({s, t} meet RightDescentSet(W, w));
    if size eq 0 or size eq 2 then
        return w, false;
    end if;

    // Factorise w into x * w_st, where w_st is in <s, t>.
    x := w;
    w_st := W.0;
    while exists(u){W.u : u in {s, t} meet RightDescentSet(W, x)} do
        x := x * u;
        w_st := u * w_st;
    end while;

    // Now the general case: build the two chains of elements.
    chain1 := [W.s];
    chain2 := [W.t];
    mst := Order(W.s * W.t);
    for i in [1 .. mst - 1] do
        Append(~chain1, chain1[i] * (i mod 2 eq 1 select W.t else W.s));
        Append(~chain2, chain2[i] * (i mod 2 eq 1 select W.s else W.t));
    end for;

    // w_st lies on one of these chains. Send it to the "opposite" end of the chain.
    _ := exists(chain){chain : chain in [chain1, chain2] | w_st in chain};
    return x * chain[mst - Index(chain, w_st)], true;
end intrinsic;

intrinsic LeftStar(W::GrpFPCox, w::GrpFPCoxElt, s::RngIntElt, t::RngIntElt) -> GrpFPCoxElt, BoolElt
{Same semantics as RightStar, but instead returning the left star *w.}
    // First deal with the minimal or maximal case.
    size := #({s, t} meet LeftDescentSet(W, w));
    if size eq 0 or size eq 2 then
        return w, false;
    end if;

    return RightStar(W, w^-1, s, t)^-1, true;
end intrinsic;

intrinsic LightLeaf(B::BSFreeCat, word::SeqEnum[RngIntElt], subexp::SeqEnum[RngIntElt]) -> BSFreeMor
{Returns the light-leaf from the Bott-Samelson object B(word) down to the subexpression word^subexp.}
    require #word eq #subexp: "Length", #word, "of word must agree with length", #subexp, "of 0-1 sequence.";
    require forall{s : s in subexp | s eq 0 or s eq 1}: "Subexp must be a 0-1 sequence.";

    // W the Coxeter group, and w is the element that the subexpression evaluates to so far.
    W := CoxeterGroup(B);
    w := W.0;
    leaf := Identity(B, []);

    for i := 1 to #word do
        si := word[i];
        ei := subexp[i];
        if #(w * W.si) gt #w then
            leaf := ei eq 0
                select leaf cat Counit(B, si)   // U0
                  else leaf cat [si];           // U1
        else
            // D0 or D1. We might need to apply some braid moves.
            _, moves := BraidToEndWith(W, Codomain(leaf), si);
            for move in moves do
                cod := Codomain(leaf);
                braid := cod[1..move[1]-1] cat Braid(B, cod[move[1]], cod[move[1] + 1]) cat cod[move[2]+1..#cod];
                leaf := braid * leaf;
            end for;

            leaf := ei eq 0
                select (Codomain(leaf)[1..#Codomain(leaf)-1] cat Mult(B, si)) * (leaf cat [si])     // D0
                  else (Codomain(leaf)[1..#Codomain(leaf)-1] cat Cap(B, si)) * (leaf cat [si]);     // D1
        end if;

        w := w * (W.si)^ei;
    end for;

    return leaf;
end intrinsic;

intrinsic LocalisedMor(B::BSCat, dom::[RngIntElt], cod::[RngIntElt]) -> BSMor
{For a generating morphism (like [s] -> [], [] -> [s, s], [s, t, s] -> [t, s, t], etc), return the
 standard morphism localising it.}
    if dom eq cod then
        return BSId(B, dom);
    end if;
    if #dom eq #cod then
        return Braid(B, dom[1], dom[2]);
    end if;
    if #dom eq 0 then
        return #cod eq 2
            select Cup(B, cod[1])
              else Unit(B, cod[1]);
    end if;
    if #cod eq 0 then
        return #dom eq 2
            select Cap(B, dom[1])
              else Counit(B, dom[1]);
    end if;
    if #dom eq 1 then
        return Comult(B, dom[1]);
    end if;
    if #cod eq 1 then
        return Mult(B, cod[1]);
    end if;

    error "Unknown generating morphism type";
end intrinsic;

// intrinsic ApplyDiagram(B::BSCat, diag::BSFreeMor, subseq::[RngIntElt]) -> BSStdMor
// {Caculate the image (bsmor) o (loc), where loc is a localised thingo.}
//     require #Domain(diag) eq #subseq: "Domain", Domain(diag), "has length incompatible with", subseq;

//     W := CoxeterGroup(B);
//     terms := AssociativeArray();
//     terms[subseq] := B`FR ! 1;

//     for row in Rows(diag) do
//         w := W.0;
//         onleft := 0;
//         for pair in row do
//             if pair[1] ne pair[2] then
//                 newTerms := AssociativeArray();
//                 mat := LocalisedMor(B, pair[1], pair[2])`stdmor`mat;
//                 for trip in Eltseq(mat) do
//                     if trip[1] ne subexpidx then
//                         continue;
//                     end if;

//             end if;

//             onleft +:= #pair[1];
//             w := w * (W ! pair[1]);
//         end for;
//     end for;

//     require (id1 cat Domain(diag) cat id2) eq loc`bsseq:
//         "Expected", loc`bsseq, "but sequence was", id1, bsmor`bsdom, id2;

//     W := B`W;
//     newTerms := AssociativeArray();
//     twist := FActionByElt(B, &*[W | W.s : s in id1]);

//     for subexp -> coeff in mor`terms do
//         subexpidx := exp2idx(subexp[#id1 + 1 .. #id1 + #bsmor`bsdom]);
//         for trip in Eltseq(bsmor`stdmor`mat) do
//             printf "(Trip, subexpidx) %o %o\n", trip, subexpidx;
//             if trip[1] ne subexpidx then
//                 continue;
//             end if;
//             newexp := subexp[1 .. #id1] cat idx2exp(trip[2], #bsmor`bscod) cat subexp[#subexp - id2 + 1 .. #subexp];
//             newTerms[newexp] := IsDefined(newTerms[newexp]) select newTerms[newexp] + coeff * twist(trip[3]) else coeff * twist(trip[3]);
//             error "Assigned term", newTerms[newexp];
//         end for;
//     end for;

//     return BSStdMorConstruct(id1 cat bsmor`bscod cat id2, newTerms);
// end intrinsic;

CanSubL:= function(seq, x)
    W := Parent(x);
    if x eq Identity(W) then return true, [0:i in [1..#seq]]; end if;
    M := { i : i in [1..#seq] | seq[i] in LeftDescentSet(W,x)};
    if IsEmpty(M) then
    return false, _;
    else
    d := Minimum(M);
    flag, d2 := $$(seq[d+1..#seq], W.seq[d]*x); // this is magma's funny syntax for recursion.
    if not flag then
        return false, _;
    else
        return true, [0 : i in [1..d-1]] cat [1] cat d2;
    end if;
    end if;
end function;

intrinsic CanonicalSubexpressionL(seq::SeqEnum, x::GrpFPCoxElt) -> BoolElt, SeqEnum
{Return the canonical subexpression (from right to left).}
    flag, sub := CanSubL(seq,x);
    if flag then
    return flag, sub;
    else
    return flag, _;
    end if;
end intrinsic;

intrinsic CanonicalSubexpression (seq::SeqEnum, x::GrpFPCoxElt) -> BoolElt, SeqEnum
{Return the canonical subexpression.}
    flag, d := CanonicalSubexpressionL(Reverse(seq), x^-1);
    if flag then
    return flag, Reverse(d);
    else
    return flag, _;
    end if;
end intrinsic;

intrinsic OldSubexpressionsEvaluatingTo(seq::SeqEnum, w::GrpFPCoxElt) -> SetEnum[SeqEnum]
{Returns all subexpressions of seq with product w.}
    W := Parent(w);
    flag, c := CanonicalSubexpression(seq,w);
    require flag: "Error: w is not less than seq.";
    current := {c};
    SubseqsSoFar := {};
    l:=#seq;
    sseq:= [ W.i : i in seq];
    repeat
    working := current;
    SubseqsSoFar := SubseqsSoFar join working;
    current := {};
    for x in working do
        for i in [1..(#seq-1)] do
        if x[i] eq 0 then // possibly we can change it to a 1.
            z := Identity(W);
            j := i+1;
            found := false;
            repeat
            if sseq[i]*z eq z*sseq[j] then
                xnew:=x;
                xnew[i] := 1;
                if xnew[j] eq 0 then xnew[j] := 1; else xnew[j] := 0; end if;
                if not (xnew in SubseqsSoFar) then current join:= {xnew}; end if;
                found := true;
            end if;
            z := z*sseq[j]^(x[j]);
            j := j+1;
            until found or j gt l;
        end if;
        end for;
    end for;
    until IsEmpty(current);
    return SubseqsSoFar;
end intrinsic;
