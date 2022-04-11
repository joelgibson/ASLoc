if assigned batch then SetQuitOnError(true); else SetDebugOnError(true); end if;
AttachSpec("ASLoc.spec");
SetColumns(0);
SetAssertions(1);
SetDebugOnError(true);
SetVerbose("IHecke", 1);

procedure Usage(missingArg)
    printf "Error: %o\n", missingArg;
    print "";
    print "Usage example: magma type:=B5 char:=2 CalcPCanIForms.m";
    print "";
    print "Arguments:";
    print "  type         (Required) Cartan type (will be fed into the CartanMatrix function).";
    print "  char         (Required) Characteristic: must be a prime number or 0.";
    print "  targetLength (Optional) Natural number: the length to calculate up to.";
    print "  showpcan     (Optional) Boolean: Print the p-canonical basis elements as they are generated.";
    print "  saveDir      (Optional) String: A directory to save progress into, which can be resumed later.";
    print "                          This directory needs to be manually created.";
    print "  profileName  (Optional) Boolean: Turn on profiling. Eg: with profileName:=prof, the profile is prof.html";
    print "  stay         (Optional) Boolean: Stay around (don't quit after calculating).";
    print "  chatty       (Optional) 1, 2, or 3: Level of chattiness, default 1.";
    quit;
end procedure;

// Read type, and print out the Dynkin diagram.
if not assigned type then Usage("Missing argument: type"); end if;
cartanMat := CartanMatrix(type);
DynkinDiagram(cartanMat);
print "";

// Read characteristic.
if not assigned char then Usage("Missing argument: char"); end if;
char := StringToInteger(char);
if not (char eq 0 or (char ge 0 and IsPrime(char))) then
    Usage("Invalid argument: char should be 0 or a prime number.");
end if;

// Read target length
targetLength := assigned targetLength
    select StringToInteger(targetLength)
    else -1;

// Switch on profiling if profileName is assigned.
if assigned profileName then
    SetProfile(true);
    procedure WriteProfile()
        name := Sprintf("CalcPCanIForms-Profile-%o-%o-%o-", type, char, profileName);
        printf "Writing profile to %o.html\n", name;
        ProfileHTMLOutput(name);
    end procedure;
else
    procedure WriteProfile()
        printf "Profiling was not enabled.\n";
    end procedure;
end if;

// Set chattiness.
chatty := assigned chatty select StringToInteger(chatty) else 1;
SetVerbose("ASLoc", chatty);

function FmtElt(w)
    return #w eq 0
        select "id"
        else   &cat[IntegerToString(i) : i in Eltseq(w)];
end function;

function isPositiveSelfDual(g)
    LPoly<v> := BaseRing(Parent(g));
    supp, coeffs := Support(g);
    for p in coeffs do
        pcoeffs := Coefficients(p);
        if not forall{x : x in pcoeffs | x ge 0} then
            return false;
        end if;
        if p ne Evaluate(p, v^-1) then
            return false;
        end if;
    end for;
    return true;
end function;

function intersectLaurentPolys(f, g)
    LPoly := Parent(f);
    return &+[LPoly
        | Min(Coefficient(f, i), Coefficient(g, i))
        : i in [Min(Valuation(f), Valuation(g)) .. Max(Degree(f), Degree(g))]
    ];
end function;

function intersectBasisSummands(C, g, h)
    // g, h should both be Hecke algebra elements in the canonical basis, which are
    // self-dual and with nonnegative coefficients.
    error if not isPositiveSelfDual(g),
        g, "is not positive self-dual";
    error if not isPositiveSelfDual(h),
        h, "is not positive self-dual";

    commonSupport := Support(g) meet Support(h);
    isect := &+[C | C.w * intersectLaurentPolys(Coefficient(g, w), Coefficient(h, w)) : w in commonSupport];
    print "Intersection of", g, "and", h, "is", isect;
    return isect;
end function;

procedure InsertBasisElement(~pC, C, aut, w, pcan, eltsToCalculate)
    // Sanity checks
    error if not isPositiveSelfDual(pcan),
        "not positive self dual";

    printf "Completed %o/%o: pC(%o) = %o\n", #pC, #eltsToCalculate, FmtElt(w), pcan;
    SetBasisElement(~pC, w, pcan);

    // If w != w^-1, we can deduce the p-canonical element for w^-1 from w.
    if w ne w^-1 and not IsDefined(pC, w^-1) then
        SetBasisElement(~pC, w^-1, &+[C | C.(y^-1) * Coefficient(pcan, y) : y in Support(pcan)]);
        printf "   Implied p-canonical basis element for its inverse %o\n", FmtElt(w^-1);
    end if;

    // If w != aut(w), we can deduce another.
    if w ne aut(w) and not IsDefined(pC, aut(w)) then
        SetBasisElement(~pC, aut(w), &+[C | C.(aut(y)) * Coefficient(pcan, y) : y in Support(pcan)]);
        printf "   Implied p-canonical basis for diagram automorphism %o\n", FmtElt(w^-1);
    end if;

    // We can perhaps even deduce another by putting these automorphisms together.
    if w ne aut(w^-1) and not IsDefined(pC, aut(w^-1)) then
        SetBasisElement(~pC, aut(w^-1), &+[C | C.(aut(y^-1)) * Coefficient(pcan, y) : y in Support(pcan)]);
        printf "   Implied p-canonical basis for diagram automorphism and inverse %o\n", FmtElt(aut(w)^-1);
    end if;
end procedure;

// Writes the pCanSoFar to a file.
procedure WriteBasis(pC, C, directory, type, p : complete:=false)
    // Serialise the basis. We would prefer to use WriteObject directly here, but there is a Magma bug blocking us, so
    // we will convert to a string and write that to a file. We need to make sure that Laurent polynomial coefficients
    // get written with a consistent name, let's choose "v".
    LPoly<v> := BaseRing(pC);
    object := SerialiseBasis(pC);


    // Since we could be overwriting an existing file, we don't want to get stuck in a situation where we
    // start overwriting all our good work, and then get killed halfway through, leaving a file which is
    // useless. Therefore we write our progress to a temporary file of a different name, and once that is
    // complete, we move the temporary file over the top of the other one. At least on UNIX systems, this move
    // is an atomic operation and will always leave us with a working file, no matter if we get killed halfway
    // through an operation.
    filename := Sprintf("%o/%o-%o.pcan", directory, type, p);
    if not complete then
        filename cat:= ".partial";
    end if;
    filenameTmp := filename cat ".tmp";

    fd := Open(filenameTmp, "w");
    fprintf fd, "%m", object;
    delete fd;
    System(Sprintf("mv \"%o\" \"%o\"", filenameTmp, filename));
    printf "%o p-canonical basis elements saved to %o\n", #pC, filename;
end procedure;

// Reads the pCanSoFar from a file, or if the file is not available do nothing.
function ReadBasis(HAlg, directory, type, p)
    filename := Sprintf("%o/%o-%o.pcan", directory, type, p);
    ok, fd := OpenTest(filename, "rb");
    if not ok then
        filename := Sprintf("%o/%o-%o.pcan.partial", directory, type, p);
        ok, fd := OpenTest(filename, "rb");
        if not ok then
            return false, false;
        end if;
    end if;

    // Read the string back in with a deterministic name for the coefficients, we're using "v".
    LPoly<v> := BaseRing(HAlg);
    pC := DeserialiseBasis(HAlg, eval Read(fd));
    delete fd;

    printf "%o p-canonical basis elements loaded from %o\n", #pC, filename;
    return pC, true;
end function;

// Set up diagrammatic category over characteristic zero (TODO: Make this more clear, and
// remove the built-in antispherical module), and the Hecke algebra from IHecke.
W := CoxeterGroup(GrpFPCox, cartanMat);
B := BSParabolic(cartanMat, W, []);
HAlg, H, C := ShortcutIHeckeAlgebra(W);

// By default we will calculate all elements of the Weyl group.
eltsToCalculate := Sort(Setseq(EnumerateCoxeterGroup(W : lengthBound := targetLength)));

// Init the pCan basis.
pC := CreateLiteralBasis(HAlg, "Canonical", "pC", Sprintf("%o-canonical basis of %o", char, type));
SetBasisElement(~pC, W.0, C.0);

// Perhaps restore a previous save.
if assigned saveDir then
    loaded, success := ReadBasis(HAlg, saveDir, type, char);
    if success then
        pC := loaded;
    end if;
end if;

// If we are in type An for n >= 2, Dn for n >= 4, or E6, then there is a nontrivial involution on the Dynkin diagram
// which gives a symmetry. (Actually in the case of D4 we get an S3 worth of symmetries, but we can do D4 very fast
// anyway, so we don't worry about this). Set aut to this involution, or the identity in other types.
function DiagramAut(W)
    id := hom<W -> W | [W.s : s in [1 .. Rank(W)]]>;

    if CartanName(W) eq "A~2" then
        return hom<W -> W | [W.2, W.1, W.3]>;
    end if;

    if not IsFinite(W) then
        return id;
    end if;

    if CartanName(W)[1] eq "A" then
        return hom<W -> W | [W.(Rank(W) - s + 1) : s in [1 .. Rank(W)]]>;
    elif CartanName(W)[1] eq "D" and Rank(W) ge 4 then
        return hom<W -> W | [W.s : s in [1 .. Rank(W) - 2] cat [Rank(W), Rank(W) - 1]]>;
    elif CartanName(W) eq "E6" then
        return hom<W -> W | [W.s : s in [6, 2, 5, 4, 3, 1]]>;
    end if;

    return id;
end function;
aut := DiagramAut(W);

torsionPrimes := {Integers() |};
ifs := 0;

knownBySupports := 0;

// We will save based on the number of elements calculated so far, or the time elapsed (whichever
// comes first).
lastSaveNum := #pC;
lastSaveTime := Realtime();

// Collect admissible pairs s, t with m_st in {3, 4, 6}.
//    m_st = 3 is always admissible.
//    m_st = 4 is admissible if p >= 3.
//    m_st = 6 is admissible if p >= 6.
admissible_orders := {3} join (char ge 3 select {4} else {}) join (char ge 5 select {6} else {});
admissible_pairs := [{s, t} : s in [1 .. Rank(W)], t in [1 .. Rank(W)] | Order(W.s * W.t) in admissible_orders];

for i -> w in eltsToCalculate do
    if IsDefined(pC, w) then
        continue;
    end if;

    // We know that for any right descent s, B(w) is a summand of B(ws) B(s), and therefore
    // we can limit the supports here.
    descElts :=
        [(C ! pC.(w * W.s)) * C.s : s in RightDescentSet(W, w)]
        cat
        [C.s * (C ! pC.(W.s * w)) : s in LeftDescentSet(W, w)];

    lrSupp := &meet[Support(h) : h in descElts];

    // For any right descent s, B(w) is a direct summand in B(ws) B(s), similarly for left descents.
    // From these we can build a table bounding the value of m_{x, w}^d for each degree d. Any pair
    // <x, w> that does not appear in the keys of the table, or appears with coefficient zero, means
    // that pC(w) is not supported there in the C basis.
    //
    // Turn all of the elements above into sets of pairs <x, deg> where <x, deg> is supported: their
    // intersection gives a bound on the support of pC(w).
    xdegsupp := &meet[
        {<x, deg> : deg in [0 .. Degree(Coefficient(h, x))], x in Support(h) | Coefficient(Coefficient(h, x), deg) ne 0}
        : h in descElts
    ];

    // If there is only one element in the support, it must be <w, 0> and we have that pCan = can for this element.
    // Early-exit here (we skip generating the Bott-Samelson Hecke algebra element in many cases).
    if #xdegsupp eq 1 then
        assert Rep(xdegsupp) eq <w, 0>;
        InsertBasisElement(~pC, C, aut, w, C.w, eltsToCalculate);
        knownBySupports +:= 1;
        continue;
    end if;

    // Now make a mapping from this support set to the minimum coefficient which appears in any of them:
    // this gives an upper bound on the m(x, w; deg) integer.
    degBoundTable := AssociativeArray();
    for h in descElts, x in Support(h), deg in [0 .. Degree(Coefficient(h, x))] do
        m_xwd := Coefficient(Coefficient(h, x), deg);
        ok, val := IsDefined(degBoundTable, <x, deg>);
        degBoundTable[<x, deg>] := ok select Min(val, m_xwd) else m_xwd;
    end for;


    // Use the right star operations to find known coefficients.
    knownCoeffs := AssociativeArray(W);
    for st in admissible_pairs do
        s, t := Explode(Setseq(st));
        wStar, ok := RightStar(W, w, s, t);

        // If w* goes up in the chain we get l(w*) > l(w), hence the m(x, w) are saying something
        // about m(x, w*) for a higher element. If w = w*, then we should get m(x*, w) = m(x, w)
        // (Are we currently exploiting this symmetry?). If l(w*) < l(w), then we can infer a bunch
        // of coefficients from elements we have already calculated.
        if ok and #wStar lt #w then
            for y in Support(C ! pC.wStar) do
                yStar, ok := RightStar(W, y, s, t);
                if ok and yStar ne wStar and #yStar lt #w then
                    knownCoeffs[yStar] := Coefficient(C ! pC.wStar, y);
                end if;
            end for;
        end if;
    end for;
    for st in admissible_pairs do
        s, t := Explode(Setseq(st));
        wStar, ok := LeftStar(W, w, s, t);
        // printf "left {%o, %o}-star of %o is %o\n", s, t, w, wStar;
        if ok and #wStar lt #w then
            for y in Support(C ! pC.wStar) do
                yStar, ok := LeftStar(W, y, s, t);
                if ok and yStar ne wStar and #yStar lt #w then
                    knownCoeffs[yStar] := Coefficient(C ! pC.wStar, y);
                end if;
            end for;
        end if;
    end for;

    // We might save here.
    if assigned saveDir and ((#pC gt lastSaveNum + 1000) or (Realtime(lastSaveTime) gt 60*5)) then
        WriteBasis(pC, C, saveDir, type, char);
        lastSaveNum := #pC;
        lastSaveTime := Realtime();
    end if;

    // Otherwise, we need to calculate some intersection forms to narrow down
    // what is possible. For each (w, deg) pair we need an intersection form to
    // tell us what more we need to take away.
    // WARNING: Need to be careful to not subtract twice here, once in the "candidate intersection"
    // and another in the intersection form.

    // Start with bigobj being the Bott-Samelson for a rex of w.
    LPoly<v> := BaseRing(C);
    word := Eltseq(w);

    // It seems like it would be a good idea to do some memoisation here to calculate the Bott-Samelsons,
    // but it is tricky to implement...
    bigobj := &*[C.s : s in Eltseq(w)];

    printf "Calculating pcan for %o\n", C.w;
    //printf "  Bott-Samelson: %o\n", bigobj;

    // Loop over the supports of the Bott-Samelson in decreasing order.
    xs := Reverse(Sort(Setseq(Support(bigobj))));
    for x in xs do
        // If this basis element is not supported over our left/right descent intersections,
        // then it must be zero. Subtract an appropriate multiple of pC(x).
        if x notin lrSupp then
            bigobj -:= Coefficient(bigobj, x) * pC.x;
            continue;
        end if;

        // If we know the value of m_{x, y} from the star operations, then make it so by
        // subtracting a multiple of pC(x).
        if IsDefined(knownCoeffs, x) then
            bigobj := bigobj + (knownCoeffs[x] - Coefficient(bigobj, x)) * pC.x;
            continue;
        end if;

        // These next two conditions seem redundant by our other heuristics, but leave them in as
        // errors for now.
        error if LeftDescentSet(W, w) notsubset LeftDescentSet(W, x),
            "descent condition";
        error if RightDescentSet(W, w) notsubset RightDescentSet(W, x),
            "descent condition";

        // Otherwise we need to look closer at this term, and calculate an intersection form to see
        // how many multiples of a shifted basis element to subtract.
        lpoly := Coefficient(bigobj, x);
        for deg in [0 .. (lpoly eq 0 select -1 else Degree(lpoly))] do
            grade := deg eq 0 select 1 else v^deg + v^-deg;
            if Coefficient(lpoly, deg) eq 0 or x eq w then
                continue;
            end if;
            ok, bound := IsDefined(degBoundTable, <x, deg>);
            if not ok or bound eq 0 then
                bigobj := C ! bigobj - Coefficient(bigobj, x, deg) * grade * pC.x;
                continue;
            end if;

            maxrank := Coefficient(Coefficient(bigobj, x), deg);

            IF := LocalIntersectionForm(B, Eltseq(w), x, deg);
            ifs +:= 1;
            rank := Rank(ChangeRing(IF, GF(char)));

            elemDivs := ElementaryDivisors(IF);
            torsionPrimes join:= {Integers() | p : p in PrimeFactors(d), d in elemDivs};

            printf "   Degree %o intersection form of %o at %o has rank %o of maximum rank %o, elementary divisor set %o\n",
                deg, FmtElt(w), FmtElt(x), rank, maxrank, Seqset(elemDivs);

            bigobj := bigobj - rank * grade * pC.x;
        end for;
    end for;
    pcan := bigobj;
    InsertBasisElement(~pC, C, aut, w, pcan, eltsToCalculate);
end for;

print "";
print "----------";
print "Complete canonical basis for", W;
for w in eltsToCalculate do
    printf "%o = %o\n", C.w, C ! pC.w;
end for;
printf "%o-canonical basis for %o\n", char, type;
print #eltsToCalculate, "elements calculated";
print ifs, "intersection forms calculated";
print &+[pC.w ne C.w select 1 else 0 : w in eltsToCalculate], "elements were different from the canonical basis";
printf "Torsion primes found: %o\n", torsionPrimes;
if forall{p : p in torsionPrimes | p lt char} then
    printf "The p-canonical basis for p >= %o is the canonical basis\n", char;
end if;

// Save if we found anything new.
if assigned saveDir and (#pC gt lastSaveNum) then
    WriteBasis(pC, C, saveDir, type, char : complete:=true);
    lastSaveNum := #pC;
    lastSaveTime := Realtime();
end if;

if assigned profileName then WriteProfile(); end if;
if not assigned stay then quit; end if;
