// TODO: Much of this file has disappeared: how much more can disappear?

import "StdCat.m": StdMorConstruct;


intrinsic DeserialisePcanIntoAS(as, r::Rec) -> Assoc
{Read the object written by SerialisePcanBasis and read the p-canonical basis into the given
antispherical module.}
    pcans := AssociativeArray();
    for t in r`pcans do
        pcans[as`W ! t[1]] := as ! t[2];
    end for;
    return pcans;
end intrinsic;

intrinsic DeserialisePcanIntoAS2(ASMod::FModIHke, r::Rec) -> Assoc
{Read the object written by SerialisePcanBasis and read the p-canonical basis into the given antispherical module.}
    pcans := AssociativeArray();
    W := CoxeterGroup(ASMod);
    C := CanonicalBasis(ASMod);
    for t in r`pcans do
        // t is of the form <elt, <elts, coeffs, basistype>>.
        elt := t[1];
        elts := t[2][1];
        coeffs := t[2][2];
        basisType := t[2][3];
        assert basisType eq "C";
        assert #elts eq #coeffs;

        pcans[W ! elt] := &+[C | C.(W ! elts[i]) * coeffs[i] : i in [1..#elts]];
    end for;
    return pcans;
end intrinsic;


// Format for serialising a ModASElt.
ModASEltRF := recformat< BasisType, Elements, Coefficients, MinValuation >;

intrinsic SerialiseRecordModASElt(h::AlgHkeElt) -> Rec
{}
    as := Parent(h);
    L := as`R;
    P := PolynomialRing(BaseRing(L));
    into := hom<L -> P | P.1>;
    elts, coeffs := Coefficients(h);
    minVal := Minimum([(coeff eq 0) select 0 else Valuation(coeff) : coeff in coeffs]);

    return rec< ModASEltRF |
        BasisType := h`BasisType,
        Elements := [Eltseq(x) : x in elts],
        Coefficients := [into(x * L.1^(-minVal)) : x in coeffs],
        MinValuation := minVal
    >;
end intrinsic;

// Format for serialising a QPDI.
// The lowerStdSeqs, homsIn, and homsOut need to be taken as a group: they are in a format
// which de-duplicates much information.
ContextRF := recformat< cartantype, cartan, sphSubset, char >;
QPDIRF := recformat< ctx, elt, stdSeq, canPol, lowerStdSeqs, homsIn, homsOut, incl, proj >;

intrinsic SerialiseRecordQPDI(indec::QPDI, char::RngIntElt) -> Rec
{}
    B := indec`Parent;

    // Collect the Weyl group elements and corresponding stdSeqs of lower hom spaces.
    lower := Sort(Setseq(Keys(indec`homsIn)));
    return rec< QPDIRF |
        ctx := rec< ContextRF |
            cartantype := CartanName(B`C),
            cartan := B`C,
            sphSubset := B`I,
            char := char
        >,
        elt := Eltseq(indec`elt),
        stdSeq := [Eltseq(x) : x in indec`stdSeq],
        canPol := SerialiseRecordModASElt(indec`canPol),
        lowerStdSeqs := [<Eltseq(x), [Eltseq(y) : y in indec`homsIn[x][1]`dom]> : x in lower],
        homsIn := [[<Eltseq(f`mat), f`deg> : f in indec`homsIn[low]] : low in lower],
        homsOut := [[<Eltseq(f`mat), f`deg> : f in indec`homsOut[low]] : low in lower],
        incl := Sort([
            <s, [Eltseq(x) : x in f`dom], [Eltseq(x) : x in f`cod], Eltseq(f`mat), f`deg>
            : s -> f in indec`incl
        ]),
        proj := Sort([
            <s, [Eltseq(x) : x in f`dom], [Eltseq(x) : x in f`cod], Eltseq(f`mat), f`deg>
            : s -> f in indec`proj
        ])
    >;
end intrinsic;



intrinsic AbsolutePath(path::MonStgElt) -> MonStgElt
{Given a relative path, return the absolute path. Removes any trailing slash.}
    output := Pipe(Sprintf("realpath \"%o\"", path), "");

    // Trim trailing newline.
    _, prefix := Regexp("[^\n]+", output);
    return prefix;
end intrinsic;

intrinsic EnsureDirectoryExists(dirname::MonStgElt)
{Ensure that a directory exists at with the given path, creating it if necessary.}
    // If directory already exists.
    if System(Sprintf("test -d \"%o\"", dirname)) eq 0 then
        return;
    end if;

    // If a file exists instead.
    if System(Sprintf("test -e \"%o\"", dirname)) eq 0 then
        error "Wanted a directory called", dirname, "but a file already exists with that name.";
    end if;

    // Try to create the directory
    if System(Sprintf("mkdir \"%o\"", dirname)) ne 0 then
        error "Could not create directory", dirname;
    end if;
end intrinsic;

intrinsic FileExists(path::MonStgElt) -> BoolElt
{Return true if path exists as a file or directory on disk.}
    return System(Sprintf("test -e \"%o\"", path)) eq 0;
end intrinsic;

intrinsic ListDirectoryFiles(dirname::MonStgElt : suffix := "", recursive := false) -> SeqEnum[MonStgElt]
{List the files (and only files) in a directory. If the suffix argument is provided, list
only files ending in that suffix. This function returns absolute paths.}
    if System(Sprintf("test -d \"%o\"", dirname)) ne 0 then
        error dirname, "is not a directory, so its contents cannot be listed.";
    end if;

    maxDepth := recursive select "" else "-maxdepth 1";

    cmd := Sprintf("find \"%o\" %o -type f -path \"*%o\"", dirname, maxDepth, suffix);
    return Sort(Split(Pipe(cmd, ""), "\n"));
end intrinsic;

intrinsic WriteObjectToFile(path::MonStgElt, obj::.)
{A helper method which uses WriteObject to write to the file.}
    f := Open(path, "w");
    WriteObject(f, obj);
    delete f;
end intrinsic;

intrinsic ReadObjectFromFile(path::MonStgElt) -> .
{A helper method which uses ReadObject to read a file.}
    f := Open(path, "r");
    return ReadObject(f);
end intrinsic;

intrinsic StringJoin(strings::SeqEnum[MonStgElt], sep::MonStgElt) -> MonStgElt
{Join the strings using the separator.}
    list := [];
    for i -> str in strings do
        Append(~list, str);
        if i ne #strings then
            Append(~list, sep);
        end if;
    end for;

    return &cat list;
end intrinsic;
