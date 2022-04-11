if assigned batch then SetQuitOnError(true); else SetDebugOnError(true); end if;

AttachSpec("ASLoc.spec");
SetColumns(0);
SetAssertions(3);

// Check one-colour relations in A2.
cartanMat := CartanMatrix("A2");
W := CoxeterGroup(GrpFPCox, cartanMat);
B := BSCategory(CartanMatrix("A2"), W);
FR := B`FR;

// Check some one-colour relations.
for s in [1 .. Rank(W)] do
    // Check cups and caps are consistent.
    assert Cup(B, s) eq Comult(B, s) * Unit(B, s);
    assert Cap(B, s) eq Counit(B, s) * Mult(B, s);

    // Barbell
    assert Counit(B, s) * Unit(B, s) eq FR.s * BSId(B);

    // Counit axiom
    assert (Counit(B, s) cat [s]) * Comult(B, s) eq BSId(B, [s]);
    assert ([s] cat Counit(B, s)) * Comult(B, s) eq BSId(B, [s]);

    // Coassociativity
    assert (Comult(B, s) cat [s]) * Comult(B, s) eq ([s] cat Comult(B, s)) * Comult(B, s);

    // Unit axiom
    assert Mult(B, s) * ([s] cat Unit(B, s)) eq BSId(B, [s]);
    assert Mult(B, s) * (Unit(B, s) cat [s]) eq BSId(B, [s]);

    // Associativity
    assert Mult(B, s) * ([s] cat Mult(B, s)) eq Mult(B, s) * (Mult(B, s) cat [s]);

    // Needle up (quidditch goal) and needle down
    assert IsZero(Cap(B, s) * Comult(B, s));
    assert IsZero(Mult(B, s) * Cup(B, s));
end for;

// Two-colour associativity for m=3
oneway := &*[
    Braid(B, 1, 2),
    Mult(B, 1) cat [2, 1]
];
otherway := &*[
    [2, 1] cat Mult(B, 2),
    Braid(B, 1, 2) cat [2],
    [1] cat Braid(B, 1, 2)
];
assert oneway eq otherway;

quit;
