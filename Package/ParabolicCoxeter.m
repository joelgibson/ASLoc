// Functions for working with quotients of Coxeter groups by parabolic subgroups.

// IsMinimal(I::SeqEnum[RngIntElt], w::GrpFPCoxElt) is an internal function provided by Magma.

intrinsic MinimalCosetRep(W::GrpFPCox, I::SeqEnum[RngIntElt], w::GrpFPCoxElt) -> GrpFPCoxElt
{Send w to its minimal coset representative.}
    if IsMinimal(I, w) then
        return w;
    end if;

    while true do
        if not exists(s){s : s in I | #(W.s * w) lt #w} then
            break;
        end if;
        w := W.s * w;
    end while;
    return w;
end intrinsic;

intrinsic ParabolicBruhatLower(W::GrpFPCox, I::SeqEnum, top::GrpFPCoxElt) -> SetEnum[GrpFPCoxElt]
{Return the set of all minimal coset representatives <= top in the Bruhat order.
Top will be sent to its minimal coset representative before starting.}
    top := MinimalCosetRep(W, I, top);
    subexprs := {W.0};
    for s in Eltseq(top) do
        subexprs := subexprs join {w * W.s : w in subexprs | IsMinimal(I, w * W.s)};
    end for;
    return subexprs;
end intrinsic;