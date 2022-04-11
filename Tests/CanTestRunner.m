// This file runs tests of QPDIndec to generate elements of the canonical (not p-canonical) basis.
// This can serve as a kind of consistency check, and does not need any extra tables of data to run
// because it is relatively easy to compute the canonical basis directly. An example invocation:
//     magma type:=A~2 param:=[0,30,0] affroot:=3 CanTestRunner.m

if assigned batch then SetQuitOnError(true); else SetDebugOnError(true); end if;

// Parse arguments.
error if not assigned type, "Need to provide a Cartan type.";
error if not assigned param, "Need to provide a param.";
error if not assigned affroot, "Need to provide an affroot.";
param := eval param;
maxrat := assigned maxrat;
affroot := eval affroot;
checkserialise := assigned checkserialise select eval checkserialise else false;
assert Type(checkserialise) eq BoolElt;

AttachSpec("ASLoc.spec");
SetColumns(0);
SetAssertions(1);

if assigned profile then
    SetProfile(true);
end if;

W := CoxeterGroup(GrpFPCox, CartanMatrix(type));
B := BSAntiSpherical(CartanMatrix(type), W, affroot);
HAlg := IHeckeAlgebra(W);
ASMod := IHeckeASMod(W, B`I);
aC := CanonicalBasis(ASMod);

maxElt := ParamToElt(W, param);
elts := Sort(Setseq(ParabolicBruhatLower(B`W, B`I, maxElt)));

printf "Will test %o indecomposables\n", #elts;

indecs := AssociativeArray();
for i -> alcove in elts do
    param := EltToParam(alcove);
    printf "Checking alcove %o/%o: %o\n", i, #elts, param;
    indecs[alcove] := calcQIndec(B, indecs, alcove, 0, HAlg, ASMod);

    error if indecs[alcove]`character ne aC.alcove,
        "p-canonical basis elements do not agree for", alcove,
        "Expected:", aC.alcove,
        "Recieved:", indecs[alcove]`character;

    if maxrat then
        print "Maximum numerator or denominator:", MaximumNumeratorOrDenominator(indecs[alcove]);
    end if;

    // TODO: Fix up serialisation.
    // if checkserialise then
    //     ser := SerialiseRecordQPDI(indecs[alcove], 0);
    //     der := DeserialiseRecordQPDI(B, 0, ser);
    //     assert indecs[alcove] eq der;
    //     print "Object serialises and deserialises correctly.";
    // end if;
end for;

printf "Checked %o canonical basis elements, all correct.\n", #elts;


if assigned profile then
    G := ProfileGraph();
    ProfileHTMLOutput(G, profile);
    printf "Profiling data written to %o.html\n", profile;
end if;

if assigned batch then quit; end if;
