// This test verifies the B3 Zamolodchikov relation, as written on page 303 of Soergel Calculus by Elias and Williamson.
if assigned batch then SetQuitOnError(true); else SetDebugOnError(true); end if;

AttachSpec("ASLoc.spec");
SetColumns(0);
SetAssertions(3);

// B3 relation, as written on page 303.
// You really need the picture to make sense of the following code. R, G, B stand for Red, Green, and Blue.
cartan := CartanMatrix("B3");
W := CoxeterGroup(GrpFPCox, cartan);
B := BSCategory(cartan, W);

g := 3;
r := 2;
b := 1;

LHS := &*[
    [g,r,g] cat Braid(B, r, b) cat [g, r, b],
    Braid(B, r, g) cat [b,r,g,r,b],
    [r,g,r] cat Braid(B,b,g) cat [r,g,r,b],
    [r,g,r,b] cat Braid(B,r,g) cat [b],
    [r,g] cat Braid(B,b,r) cat [g,r] cat Braid(B,b,g),
    [r] cat Braid(B, b,g) cat [r] cat Braid(B, g,b) cat [r,b,g],
    [r,b,g,r,g] cat Braid(B, r,b) cat [g],
    [r,b] cat Braid(B,r,g) cat [b,r,g],
    Braid(B,b,r) cat [g,r] cat Braid(B,b,g) cat [r,g],
    [b,r] cat Braid(B,g,b) cat [r,b,g,r,g]
];

RHS :=&*[
    [g,r,g,b,r] cat Braid(B,g,b) cat [r,b],
    [g,r] cat Braid(B,b,g) cat [r,g] cat Braid(B,r,b),
    [g,r,b] cat Braid(B,r,g) cat [b,r],
    [g] cat Braid(B,b,r) cat [g,r] cat Braid(B,b,g) cat [r],
    [g,b,r] cat Braid(B,g,b) cat [r,b,g,r],
    [g,b,r,g] cat Braid(B,r,b) cat [g,r],
    Braid(B,b,g) cat [r,g,r,b,r,g,r],
    [b] cat Braid(B,r,g) cat [b,r,g,r],
    [b,r,g,r] cat Braid(B,b,g) cat [r,g,r],
    [b,r,g,r,b] cat Braid(B,r,g),
    [b,r,g] cat Braid(B,b,r) cat [g,r,g]
];

assert LHS eq RHS;

quit;
