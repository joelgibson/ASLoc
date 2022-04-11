// This file uses pDIndec to generate a table of p-canonical basis elements. This table is used in
// PcanTestRunner.m to test new methods of calculating p-canonical basis elements.

SetColumns(0);
SetDebugOnError(true);

type := "C2";
AttachSpec(Sprintf("../%o.spec", type));

if type eq "A2" then
    C := Matrix(Integers(), CartanMatrix("A~2"));
    p := 3;
    W := CoxeterGroup(GrpFPCox, C);
    as := AntiSphericalModule(W, [1,2]: char := p);
    D := DiagASCat(as : char := p);
    target := [20, 0, 0];
end if;

if type eq "C2" then
    C := Matrix(Integers(), CartanMatrix("C~2"));
    p := 3;
    W := CoxeterGroup(GrpFPCox, C);
    as := AntiSphericalModule(W, [1,2]: char := p);
    D := DiagASCat(as : char := p);
    target := [0, 20, 0];
end if;

if type eq "G2" then
    C := Matrix(Integers(), CartanMatrix("G~2"));
    p := 11;
    W := CoxeterGroup(GrpFPCox, C);
    as := AntiSphericalModule(W, [1,2]: char := p);
    D := DiagASCat(as : char := p);
    target := [0, 10, 0];
end if;


printf "Generating tests for type %o, p = %o, up to %o\n", CartanName(C), p, target;


pcans := AssociativeArray();
alcoveElts := Sort(Setseq(ParabolicBruhatLower(W, as`SphericalSubset, W ! ParamToRex(target))));
for i -> alcoveElt in alcoveElts do
    alcove := wToParam(as, alcoveElt);
    printf "Calculating pDIndec %o/%o: %o\n", i, #alcoveElts, alcove;
    calcIndecObj(~D, alcove);
    pcans[alcoveElt] := getChar(as, D`pIndecObjs[alcove]);
    start := Realtime();
    x := 1 + 1;
    ending := Realtime();
    printf "Time: %o sec\n", ending - start;
end for;

// Serialise, check that the serialisation worked.
ser := SerialisePcanBasis(C, as`SphericalSubset, p, pcans);
der := DeserialisePcanIntoAS(as, eval ser);
assert Keys(pcans) eq Keys(der);
assert forall{pcans[k] eq der[k] : k in Keys(pcans)};

filename := Sprintf("pcan-%o-%o-upto-%o-%o-%o",
    CartanName(as`CoxeterGroup), as`char, target[1], target[2], target[3]);
PrintFile(filename, ser : Overwrite := true);
print "Output written to", filename;

quit;