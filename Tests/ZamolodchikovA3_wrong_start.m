// This test verifies the A3 Zamolodchikov relation, as written on page g0 of Soergel Calculus by Elias and Williamson.
if assigned batch then SetQuitOnError(true); else SetDebugOnError(true); end if;

AttachSpec("ASLoc.spec");
SetColumns(0);
SetAssertions(3);

// A3 relation, as written on page 10.
// You really need the picture to make sense of the following code. R, G, B stand for Red, Green, and Blue.
cartan := CartanMatrix("A3");
W := CoxeterGroup(GrpFPCox, cartan);
B := BSCategory(cartan, W);

g := 1;
r := 2;
b := 3;

LHS := &*[
    [r, g] cat Braid(B, b, r) cat [g],
    [r] cat Braid(B, b, g) cat [r] cat Braid(B, g, b),
    [r, b] cat Braid(B, r, g) cat [b],
    Braid(B, b, r) cat [g, r, b],
    [b, r] cat Braid(B, g, b) cat [r, b],
    [b, r, g] cat Braid(B, r, b)
];
RHS :=&*[
    Braid(B, g, r) cat [b, r, g],
    [g, r] cat Braid(B, b, g) cat [r, g],
    [g, r, b] cat Braid(B, r, g),
    [g] cat Braid(B, b, r) cat [g, r],
    Braid(B, b, g) cat [r] cat Braid(B, g, b) cat [r],
    [b] cat Braid(B, r, g) cat [b, r]
];
assert LHS eq RHS;

quit;
