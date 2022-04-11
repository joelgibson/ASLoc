if assigned batch then SetQuitOnError(true); else SetDebugOnError(true); end if;
AttachSpec("ASLoc.spec");
SetColumns(0);
SetAssertions(1);
SetDebugOnError(true);

procedure Usage(missingArg)
    printf "Error: %o\n", missingArg;
    print "";
    print "Usage example: magma type:=A~2 I:=[1,2] char:=5 target:=[10,10,0] CalculateIndec.m";
    print "";
    print "Arguments:";
    print "  type      (Required) Cartan type (will be fed into the CartanMatrix function).";
    print "  I         (Required) Generating set for parabolic subgroup. May be empty.";
    print "                       If I is maximal, the rational optimisation will be applied.";
    print "  char      (Required) Characteristic: must be a prime number or 0.";
    print "  target    (        ) Generate indecomposables <= target. Required for infinite groups.";
    print "                       Defaults to the longest element for finite groups.";
    print "  showpcan  (Optional) Boolean: Print the p-canonical basis elements as they are generated.";
    // TODO: Fix up saving!
    // print "  datadir   (Optional) String: Directory to save the p-canonical basis into.";
    // print "  saveindec (Optional) Boolean: true will also save indecomposables to datadir, and load";
    // print "                       any available before starting the computation.";
    print "  modular   (Optional) Boolean: Work over the finite field F_p rather than Z_(p). This does not always work!";
    print "  profile   (Optional) Boolean: Turn on profiling. If profile:=prof, the profile is written";
    print "                       to prof.html at the conclusion of the program.";
    print "  maxrat    (Optional) Boolean: Print maximum numerator or denominator appearing in the hom";
    print "                       spaces for the indecomposable.";
    print "  stay         (Optional) Boolean: Stay around (don't quit after calculating).";
    quit;
end procedure;

// type or cartan
if not assigned type then Usage("Missing argument: type"); end if;
cartan := CartanMatrix2(type);
DynkinDiagram(cartan);
print "";

// I
if not assigned I then Usage("Missing argument: I"); end if;
I := eval I;
if #I gt 0 and ExtendedType(I) ne SeqEnum[RngIntElt] then
    Usage("Invalid: I should be a sequence of integers.");
end if;
I := Sort(Setseq({i : i in I}));

// char
if not assigned char then Usage("Missing argument: char"); end if;
char := StringToInteger(char);
if not (char eq 0 or (char ge 0 and IsPrime(char))) then
    Usage("Invalid argument: char should be 0 or a prime number.");
end if;

// Construct the category, Coxeter group, and antispherical module.
W := CoxeterGroup(GrpFPCox, cartan);
HAlg := IHeckeAlgebra(W);
ASMod, aH, aC := ShortcutIHeckeASMod(W, I);

if assigned modular then
    B := BSFiniteField(cartan, W, I, char);
else
    B := BSParabolic(cartan, W, I);
end if;


// Create a context object which we can save.
ContextRF := recformat< cartantype, cartan, sphSubset, char >;
context := rec< ContextRF |
    cartantype := type,
    cartan := cartan,
    sphSubset := I,
    char := char
>;

// target
if not assigned target and not IsFinite(W) then
    Usage("Missing argument: target (must be defined when W is infinite)");
elif assigned target then
    target := ParamToElt(W, eval target);
else
    target := MinimalCosetRep(W, I, LongestElement(W));
end if;

if not IsMinimal(B`I, target) then
    printf "target %o is not minimal.\n", target;
    target := MinimalCosetRep(W, I, target);
    printf "changed to %o\n", target;
end if;

// showpcan
if assigned showpcan then
    if showpcan notin {"true", "false"} then
        Usage("Invalid argument: showpcan (should be true or false)");
    end if;
end if;
showpcan := assigned showpcan select eval showpcan else false;

// Build a string describing the parameters, which we will use if saving/loading.
paramStr := Sprintf("type.%o.I.%o.char.%o",
    type, (#I gt 0) select &cat[IntegerToString(i) : i in I] else "", char);

// datadir
if assigned datadir then
    datadir := AbsolutePath(datadir);
    EnsureDirectoryExists(datadir);
    saveDir := AbsolutePath(datadir) cat "/" cat paramStr cat "/";
    EnsureDirectoryExists(saveDir);
    savePCan := true;

    print "As they are generated, p-canonical basis elements will be saved to %o\n", saveDir;
    WriteObjectToFile(saveDir cat "context", context);
else
    saveDir := "";
    savePCan := false;
end if;
savedCanCounter := 0;

// saveindec
if assigned saveindec then
    if saveindec notin {"true", "false"} then
        Usage("Invalid argument: saveindec (should be true or false)");
    end if;
    saveindec := eval saveindec;
else
    saveindec := false;
end if;

if saveindec and not assigned datadir then
    Usage("Invalid argument: saveindec can only be used in conjunction with datadir.");
end if;

if saveindec then
    printf "As they are generated, indecomposables will be saved to %o\n", saveDir;
end if;
savedIndecCounter := 0;

// profile
if assigned profile then
    SetProfile(true);
    printf "Profiling enabled: on completion profile will be written to %o.html\n", profile;
end if;

// Show Dynkin diagram etc for clarity.
printf "Computing in type %o and characteristic %o\n", type, char;
printf "Parabolic quotient is by %o\n", I;
printf "Hom-spaces are matrices over %o\n", B`Q;

elts := Sort(Setseq(ParabolicBruhatLower(B`W, B`I, target)));
indecs := AssociativeArray();
apC := CreateLiteralBasis(ASMod, "Canonical", "apC", Sprintf("%o-canonical basis of %o", char, type));

// See if we can load indecomposable objects from file.
// if saveindec then
//     dirContext := ReadObjectFromFile(saveDir cat "context");
//     error if (
//         dirContext`cartan ne context`cartan or
//         dirContext`sphSubset ne context`sphSubset or
//         dirContext`char ne context`char
//     ),
//         "Current context was", context,
//         "but context saved in", saveDir, "is", dirContext;

//     indecPaths := Seqset(ListDirectoryFiles(saveDir : suffix := ".indec"));
//     eltPaths := {saveDir cat EltToParamStr(elt) cat ".indec" : elt in elts};
//     commonPaths := indecPaths meet eltPaths;
//     for path in commonPaths do
//         indec := DeserialiseRecordQPDI(B, char, ReadObjectFromFile(path));
//         indecs[indec`elt] := indec;
//         pcans[indec`elt] := indec`canPol;
//     end for;
//     print #commonPaths, "indecomposables loaded from", saveDir;
// end if;

printf "%o indecomposables to generate.\n", #elts - #indecs;

for i -> elt in elts do
    if IsDefined(indecs, elt) then
        if showpcan then
            printf "p-canonical elt: %o\n", aC ! indecs[elt]`character;
        end if;
        continue; // Already loaded.
    end if;

    indecs[elt] := calcQIndec(B, indecs, elt, char, HAlg, ASMod);
    SetBasisElement(~apC, elt, indecs[elt]`character);
    printf "%o/%o %o calculated", i, #elts, EltToParamStr(elt);
    if showpcan then
        printf " : %o\n", aC ! indecs[elt]`character;
    else
        printf "\n";
    end if;

    if assigned maxrat then
        print "Maximum numerator or denominator   :", MaximumNumeratorOrDenominator(indecs[elt]);
    end if;

    if savePCan then
        path := saveDir cat EltToParamStr(elt) cat ".pcan";
        if not FileExists(path) then
            WriteObjectToFile(path, <Eltseq(elt), SerialiseRecordModASElt(indecs[elt]`character)>);
            savedCanCounter +:= 1;
        end if;
    end if;

    if saveindec then
        path := saveDir cat EltToParamStr(elt) cat ".indec";
        if not FileExists(path) then
            WriteObjectToFile(path, SerialiseRecordQPDI(indecs[elt], char));
            savedIndecCounter +:= 1;
        end if;
    end if;
end for;

if savePCan then
    printf "%o new p-canonical basis elements were written to %o\n", savedCanCounter, saveDir;
end if;
if saveindec then
    printf "%o new indecomposable objects were written to %o\n", savedIndecCounter, saveDir;
end if;

if assigned profile then
    G := ProfileGraph();
    ProfileHTMLOutput(G, profile);
    printf "Profiling data written to %o.html\n", profile;
end if;

if not assigned stay then quit; end if;
