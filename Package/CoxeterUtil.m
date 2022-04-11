// For type independence, we need to have a way of calculating parametrisations of Coxeter elements
// which is not strictly tied to a Spec file. There are three ways:
// 1. Lex order: the lexicographically smallest reduced word.
// 2. Reverse lex order: the lexicographically greatest reduced word.
// 3. Box parametrisation (applies to affine groups only, and even then after choosing a labelling of the box).

function EltToParamAffA2Box(W, w)
    W := Parent(w);
    //require IsMinimal(W, AS`SphericalSubset, w): "w must be minimal in its left coset.";
    seq := Eltseq(w);
    if HasUniqueRex(W, w) or (w eq W!1)  then
        if #seq eq 0 then return [0,0,0]; end if;
        if #seq eq 1 then return [0,0,1]; end if;
        if seq[1..2] eq [3,2] then
            return [#seq div 2, 0, #seq mod 2];
        else
           return [0, #seq div 2, #seq mod 2];
        end if;
    else
        ds := RightDescentSet(W,w);
        if #ds eq 1 then
            ds := Setseq(ds);
            r := ds[1];

            // In A~2, only the elements [x, y, 1] have a right descent set of cardinality 1.
            // Just reduce them in each column.

            BaseSeq := [1,2,3];
            index := Index(BaseSeq, r);
            if index eq 1 then
                t := BaseSeq[3];
            else
                t := BaseSeq[index - 1];
            end if;

            param := EltToParamAffA2Box(W, w * W.r * W.t);
            return [param[1], param[2] + 1, param[3]];
        else
            u := W.(Setseq({1,2,3} diff ds)[1]);
            // For A~2 do:
            // In each fundamental box, the first element has a right descent set of cardinality 2.
            ds := Setseq(ds);
            s := W.ds[1];
            t := W.ds[2];
            param := EltToParamAffA2Box(W, w*s*t*s*u);
            return [param[1] + 1, param[2] + 1, 0];
           end if;
    end if;
end function;

function ParamToRexAffA2Box(param)
    FB := [ PowerSequence(IntegerRing()) |  \[], \[3]];
    lengths := [Integers() | 2, 2];
    wts := [Rationals() | 1001, 1000, 500];
    O1 := func< l | [i mod 3 + 1 : i in [-1 .. -l by -1]]>; // [3, 2, 1, 3, 2, 1, ...]
    O2 := func< l | [i mod 3 + 1 : i in [2 .. l+1]]>;       // [3, 1, 2, 3, 1, 2, ...]
    o1 := SymmetricGroup(3)!(1,2,3);
    o2 := SymmetricGroup(3)!(1,3,2);

    elt := function(a, b, fb)
        return ( O1(lengths[1]*a) cat O2(lengths[2]*b)^(o1^a) cat fb^(o1^a*o2^b) );
    end function;

    return elt(param[1], param[2], FB[param[#param] + 1]);
end function;

function EltToParamAffC2Box(W, w)
    //require IsMinimal(W, AS`SphericalSubset, w): "w must be minimal in its left coset.";
    seq := Eltseq(w);
    if HasUniqueRex(W, w) or (w eq W!1)  then
        // if RightDescentSet(W, w) eq {1,3} then
        if w eq W![3,1,3] then
            // w is the only antispherical element with a unique rex that does not lie on the
            // wall we're interested in
            // printf "Elt reduces to %o", [0, 1, 0];
            return [0, 1, 0];
        else
            // printf "Elt reduces to %o", [#seq div 4, 0, #seq mod 4];
            return [#seq div 4, 0, #seq mod 4];
        end if;
    else
        ds := RightDescentSet(W,w);
        if #ds eq 1 then
            ds := Setseq(ds);

            // In B~2, only the elements [x, y, i] with 2<=i<=3 and [0, k, 0] for k>=0
            // have a right descent set of cardinality 1... Just reduce them
            // in each column.
            if 1 in ds then
                param := EltToParamAffC2Box(W, w*W.1*W.2*W.3);
                return [param[1], param[2] + 1, param[3]];
            else
                r := W.(ds[1]);
                s := W.1;
                param := EltToParamAffC2Box(W, w*r*s*r);
                return [param[1], param[2] + 1, param[3]];
            end if;
        else
            u := W.(Setseq({1,2,3} diff ds)[1]);

            // In each fundamental box, there are at most two elements with a right
            // descent set of cardinality 2.
            // The first element in each fundamental box can be recognized by checking that 1
            // is in its right descent set, as the two subsets generating the finite Weyl
            // group are {1,2} and {1,3} and the second element always has {2,3} as right descent set.
            if 1 in ds then
                t := W.(Setseq(ds diff {1})[1]);
                s := W.1;
                param := EltToParamAffC2Box(W, w*t*s*t);
                error if (param[3] ne 0), "This has to be the first element in its fundamental box!";
                return [param[1], param[2] + 1, 0];
            else
                ds := Setseq(ds);
                s := W.ds[1];
                t := W.ds[2];
                param := EltToParamAffC2Box(W, w*t*s*u);
                error if (param[3] ne 1), "This has to be the second element in its fundamental     box!";
                return [param[1], param[2] + 1, 1];
            end if;
        end if;
    end if;
end function;

function ParamToRexAffC2Box(param)
    FB := [ PowerSequence(IntegerRing()) | \[], \[3], \[3,1], \[3,1,2]];
    lengths := [Integers() | 4, 3];
    O1patt := \[3,1,2,1];
    O2patt := \[3,1,3,2,1,2];
    O1 := func< l | [O1patt[1 + (i mod #O1patt)] : i in [0 .. l-1]] >;
    O2 := func< l | [O2patt[1 + (i mod #O2patt)] : i in [0 .. l-1]] >;
    p := SymmetricGroup(3)!(2,3);

    elt := function(a, b, fb)
        return ( O1(lengths[1]*a) cat O2(lengths[2]*b) cat fb^(p^b) );
    end function;

    return elt(param[1], param[2], FB[param[#param] + 1]);
end function;

intrinsic EltToParam(w::GrpFPCoxElt) -> SeqEnum[RngIntElt]
{}
    W := Parent(w);

    // First try to apply the box parametrisation
    case CartanName(W):
        when "A~2": return EltToParamAffA2Box(W, w);
        when "C~2": return EltToParamAffC2Box(W, w);
    end case;

    // Fall back to lex order.
    return Eltseq(w);
end intrinsic;

function BoxToStr(param)
    out := "";
    for i -> x in param[1..#param-1] do
        out cat:= IntegerToString(x);
        out cat:= ".";
    end for;
    return out cat CodeToString(StringToCode("a") + param[#param]);
end function;

intrinsic EltToParamStr(w::GrpFPCoxElt) -> MonStgElt
{}
    W := Parent(w);

    // First try to apply the box parametrisation
    case CartanName(W):
        when "A~2": return BoxToStr(EltToParamAffA2Box(W, w));
        when "C~2": return BoxToStr(EltToParamAffC2Box(W, w));
    end case;

    // Fall back to lex order.
    return #w eq 0
        select "id"
        else   &cat[IntegerToString(s) : s in Eltseq(w)];
end intrinsic;

intrinsic ParamToElt(W::GrpFPCox, param::SeqEnum[RngIntElt]) -> GrpFPCoxElt
{}
    // First try to apply the box parametrisation
    case CartanName(W):
        when "A~2": return W ! ParamToRexAffA2Box(param);
        when "C~2": return W ! ParamToRexAffC2Box(param);
    end case;

    // Fall back to lex order.
    return W ! param;
end intrinsic;

intrinsic CartanMatrix2(str::MonStgElt) -> Mtrx
{Return a Cartan matrix of the given type. If the type is followed by !, then
the labelling is reversed.}
    if #str gt 3 and str[#str-2 .. #str] eq "rev" then
        str := str[1 .. #str - 3];
        reverse := true;
    else
        reverse := false;
    end if;

    mat := Matrix(Integers(), CartanMatrix(str));

    if reverse then
        w0 := Sym(Nrows(mat)) ! [Nrows(mat) .. 1 by -1];
        perm := PermutationMatrix(Integers(), w0);
        return perm * mat * perm;
    end if;
    return mat;
end intrinsic;
