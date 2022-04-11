if assigned batch then SetQuitOnError(true); else SetDebugOnError(true); end if;

AttachSpec("ASLoc.spec");
SetColumns(0);
SetAssertions(3);

// This test file follows the one-colour maps and relations in Section 2 of
// Localized Calculus for the Hecke Category, by Elias and Williamson.

R<x> := RationalFunctionField(Rationals());
W := CoxeterGroup(GrpFPCox, CartanMatrix("A1"));
act := function(w)
    if w eq W.1 then
        return hom< R -> R | -x >;
    else
        return hom< R -> R | x >;
    end if;
end function;

id := W.0;
s := W.1;

Bsid := StdMorphism(R, [id, s]);
counit := StdMorphism(R, [id, s], [id], [[x], [0]]);
unit := StdMorphism(R, [id], [id, s], [[1, 0]]);
comult := StdMorphism(R, [id, s], [id, s, s, id], [
    [1/x,   0,    0, -1/x],
    [0,   1/x, -1/x,    0]
]);
mult := StdMorphism(R, [id, s, s, id], [id, s], [
    [1, 0],
    [0, 1],
    [0, 1],
    [1, 0]
]);
cup := comult * unit;
cap := counit * mult;

// Check getters are working.
assert Domain(counit) eq [id, s];
assert Codomain(counit) eq [id];

// Barbell relation
assert counit * unit eq x * StdMorphism(R, [id]);

// Counit relations
assert Tensor(act, counit, [id, s]) * comult eq Bsid;
assert Tensor(act, [id, s], counit) * comult eq Bsid;

// Coassociativity
assert Tensor(act, comult, [id, s]) * comult eq Tensor(act, [id, s], comult) * comult;

// Unit relations
assert mult * Tensor(act, [id, s], unit) eq Bsid;
assert mult * Tensor(act, unit, [id, s]) eq Bsid;

// Cups and caps are as we expect.
assert Matrix(cup) eq Matrix([[1/x, 0, 0, -1/x]]);
assert Matrix(cap) eq Matrix([[x], [0], [0], [x]]);

// Tensor products twist morphisms correctly. (When following the paper, note that
// matrix entries that must be zero since the row object is unqual to the column object
// are omitted entirely, so while a 4x2 matrix is shown, an 8x2 matrix is meant).
assert Matrix(Tensor(act, [id, s], cup)) eq Matrix([
    [1/x, 0, 0, -1/x,    0, 0, 0,   0],
    [  0, 0, 0,   0, -1/x,  0, 0, 1/x]
]);

// For some reason I can't put these in a sequence? Needed to define IsCoercible. Leave
// this line in the tests to make sure nothing weird happens when putting them in a sequence.
seq := [unit, counit];

quit;
