# ASLoc

A MAGMA package for working with the localised diagrammatic category and calculating the p-canonical basis of Hecke
algebras.

By Joel Gibson, Lars Thorge Jensen, and Geordie Williamson, 2022.


- [ASLoc](#asloc)
- [Overview](#overview)
- [Installation](#installation)
  - [Running tests](#running-tests)
- [Calculating p-canonical antispherical bases for affine groups](#calculating-p-canonical-antispherical-bases-for-affine-groups)
  - [Basic usage](#basic-usage)
  - [Using the basis afterwards](#using-the-basis-afterwards)
  - [Modular mode](#modular-mode)
  - [Saving progress](#saving-progress)
- [Calculating p-canonical bases for finite groups](#calculating-p-canonical-bases-for-finite-groups)
  - [Basic usage](#basic-usage-1)
  - [Using the basis afterwards](#using-the-basis-afterwards-1)
  - [Saving progress](#saving-progress-1)
  - [Showing progress](#showing-progress)
- [Calculations in the diagrammatic category](#calculations-in-the-diagrammatic-category)
  - [A local intersection form](#a-local-intersection-form)
  - [Verifying relations](#verifying-relations)
- [Future work](#future-work)
- [Technical notes](#technical-notes)


# Overview

`ASLoc` contains an implementation of the *localised* diagrammatic category, which it uses to calculate p-canonical
bases of Hecke algebras. A user of this package should be familiar with Coxeter groups and Hecke algebras, while someone
wanting to read or work on the internals should be comfortable with the diagrammatic category: at least parts I and II
of [Introduction to Soergel Bimodules](https://link.springer.com/book/10.1007/978-3-030-48826-0), along with the basic
theory and results of the modular case.

The algorithms used are explained in the paper [*Calculating the p-canonical basis of Hecke algebras*](https://arxiv.org/abs/2204.04924). There are two main algorithms, one more adapted to the case of affine groups (affine ranks 2 and 3), and the other more
adapted to small rank finite groups (up to rank 6 ish).

The Hecke algebra aspects of `ASLoc` (which are actually quite small) rely on the
[IHecke](https://github.com/joelgibson/IHecke) package, which is imported as a submodule.


# Installation

You will need an up-to-date version of [Magma](http://magma.maths.usyd.edu.au/magma/): we have tested with V2.26-11.

The repository can be cloned using `git`.
Since it contains the [IHecke](https://github.com/joelgibson/IHecke) library as a submodule, use the following command
to download ASLoc and IHecke at the same time:

    git clone --recurse-submodules https://github.com/joelgibson/ASLoc

Change into the ASLoc directory, and try one of the examples below.


## Running tests

Test that the examples in this readme file are up-to-date:

    python3 IHecke/test-readme.py

Run longer tests (runs various tests simultaneously):

    python3 run_tests.py

The linting script `python3 lint.py` checks to make sure that there are no tabs used, and that lines don't have trailing
spaces, etc: these are easy to fix. It also lists wherever a `TODO` appears in the code, which is a bit harder to fix...


# Calculating p-canonical antispherical bases for affine groups

The [`CalcIndec`](CalcIndec.m) program is suited to calculating the p-canonical basis for affine groups of small rank.


## Basic usage

To calculate p-canonical antispherical bases in an affine group, we need to specify the `type` of the group (eg `A~2`),
the generators `I` for the parabolic quotient (this should be `[1,2]` for an affine rank 2 group, since by the Magma
numbering conventions the affine root is numbered last), and the `target` element to calculate up to. For finite groups,
the `target` is given as a reduced expression, or can be omitted. For affine rank 2 groups, it should be an element in
"box notation", for instance `[7, 2, 0]` would try to calculate out the the fundamental weight (7, 2). (Don't worry
about the last coordinate, this is non-canonically indexing the alcoves in a box).

> Switching between reduced expression and box notation is not done well, and doesn't make a whole lot of sense.

We also (of course) need to give the `char` argument, giving the characteristic and putting the "p" into "p-canonical
basis". With this information, the program can kick off and start generating indecomposable objects, and taking their
character to get p-canonical basis elements. The command

    $ magma -b type:=A~2 I:=[1,2] char:=3 target:=[5,5,0] CalcIndec.m

will calculate all 3-canonical basis elements in the antispherical module of affine type A2 corresponding to the
quotient of the finite Weyl group, for all elements that are Bruhat less-or-equal-to the alcove touching the weight
(5, 5). This should only take a few seconds, but it won't show any of the basis elements (they grow very quickly, and
are annoying to write out for larger cases). To see them, pass the `showpcan:=true` argument too:

    $ magma -b type:=A~2 I:=[1,2] char:=3 target:=[5,5,0] showpcan:=true CalcIndec.m


## Using the basis afterwards

The program exits at the end of the computation: in order to make it stay around for interactive use, pass `stay:=true`.
At the conclusion of the main program, the antispherical p-canonical basis is saved in the `paC` basis, and then `aH`
and `aC` bases are the standard and canonical bases of the Hecke algebra, respectively.

    $ magma -b type:=A~2 I:=[1,2] char:=3 target:=[5,5,0] stay:=true CalcIndec.m
    ...
    > // Express a p-canonical basis element in the canonical basis
    > aC ! apC.[3,1,2,3,1,2,3,1];
    (1)aC(31231231) + (1)aC(312131)

    > // Express a canonical basis element in the p-canonical basis.
    > apC ! aC.[3,1,2,3,1,2,3,1];
    (1)apC(31231231) + (-1)apC(312131)


## Modular mode

For reasons explained in our paper, the antispherical algorithm operates over a characteristic zero local ring with
residue field F_p, rather than over the finite field F_p. When the program starts up, it will say something like:

    Hom-spaces are matrices over Rational Field

because internally it is representing hom spaces as Z_(p)-lattices inside Q (where Z_(p) denotes the subring of
rationals whose denominators are not divisible by p). Technically here we are considering the antispherical category
defined over Z_(p), and using a theoretical result that upon base change to F_p the indecomposables remain
indecomposable.

The reason that we need to work this way is that the antispherical quotient needs to zero some root coefficients and
have the root remain nonzero. This is sometimes a problem: for example if (2, 1) is a root coefficient and the
antispherical quotient wants to send it to (2, 0), then we need to be working outside of characteristic 2, otherwise the result is (0, 0) and the localisation will not work properly.

If you are working in a setting where this will not happen (for example when there is no antispherical quotient  `I:=[]`,
or if you have chosen your quotient carefully in a finite type group), then passing `modular:=true` can speed up this
algorithm quite a lot. When the program starts up you will instead see something like

    Hom-spaces are matrices over Multivariate rational function field of rank 3 over GF(3)

meaning that it is now working over F_p. If you have not satisfied the conditions above, the algorithm *should* fail an
integrity check, outputting something like

    Runtime error: Characters in and out disagree

but we do not guarantee that any misuse of `modular:=true` is caught by these integrity checks.

In summary:

- If there is no antispherical quotient (`I:=[]`), then it is always ok to use `modular:=true`.
- If there is an antispherical quotient like `I:=[1]`, then it is ok to use `modular:=true`, provided that all the root
  coefficients in the root system, modulo p, and with the first coordinate cut off, are nonzero.


## Saving progress

Saving progress of this algorithm is a little gnarly at the moment, there is some commented-out code which used to work,
and can be made to work with some modifications. This is high on the list of things to fix! The problem is that it is
not enough to save only the p-canonical basis elements, but one needs to also save the indecomposable objects, and so
there is a lot of book-keeping to do. It also seems that having available RAM is really the limiting factor of this
algorithm, rather than time, and so being able to save progress has some diminishing returns.


# Calculating p-canonical bases for finite groups

The [`CalcPCanIForms`](./CalcPCanIForms.m) program is suited to calculating the p-canonical basis for finite groups: we
have successfully used this to calculate the p-canonical basis (and found all the torsion primes) for the finite Weyl
groups of rank <= 6, as well as A7. These calculations (or at least the resulting p-cells) appeared in the Appendix of
[Categorical Diagonalisation and p-Cells](https://arxiv.org/abs/2111.12190) by Ben Elias and Lars Thorge Jensen, with
Joel Gibson as the Appendix author.


## Basic usage

There are some usage notes at the top of the file. A typical usage looks like this:

    $ magma -b type:=G2 char:=2 CalcPCanIForms.m

The program will print some progress data, and when it is complete it will print the whole 2-canonical basis with some
concluding remarks:

    2-canonical basis for G2
    12 elements calculated
    7 intersection forms calculated
    4 elements were different from the canonical basis
    Torsion primes found: { 2, 3 }

The 12 elements calculated are the 12 elements of the group G2. The number of intersection forms calculated is how many
intersection forms were actually needed by the algorithm (many can be skipped by using inverse symmetries, Dynkin
diagram automorphisms, or the star operations, although the star operations are quite restricted in characteristics 2
and 3). There were four elements different from the canonical basis, so the 2-canonical basis of G2 is genuinely
different from the canonical basis.

Finally the torsion primes found are listed. These are *not necessarily* the torsion primes for the whole of G2, since
the direction of the algorithm will change as soon as the first torsion in the given characteristic is found. To get the
full set of torsion primes, make the characteristic high enough that the p-canonical basis becomes the canonical basis.
For G2 for instance, we have

    $ magma -b type:=G2 char:=5 CalcPCanIForms.m
    ...
    0 elements were different from the canonical basis
    Torsion primes found: { 2, 3 }
    The p-canonical basis for p >= 5 is the canonical basis

Here the 5-canonical basis coincides with the canonical basis, and the torsion primes encountered along the way were 2
and 3. However, because the characteristic we are working in did not coincide with any of these, the program can now
conclude that we have found the whole set of torsion primes.


## Using the basis afterwards

Pass `stay:=true` to the `CalcPCanIForms` program to make it "stay around" and not quit after computation. The
p-canonical basis will be loaded into a variable called `pC`, with the standard and canonical bases loaded into `H` and
`C` respectively. Using the same G2 example from before, but passing `stay:=true`:

    $ magma -b type:=G2 char:=2 stay:=true CalcPCanIForms.m
    ...
    > pC.[1,2,1,2];
    (1)pC(1212)
    > C ! pC.[1,2,1,2];
    (1)C(1212) + (1)C(12)
    > H ! pC.[1,2,1,2];
    (1)H(1212) + (v)H(212) + (v)H(121) + (v^2)H(21) + (1 + v^2)H(12) + (v + v^3)H(2) + (v + v^3)H(1) + (v^2 + v^4)H(id)

The basis `pC` is a "literal" basis in [IHecke](https://github.com/joelgibson/IHecke): follow the IHecke documentation
to learn how to manipulate these.


## Saving progress

The 3-canonical bases in types B6 and C6 take hours to compute, and the 2-canonical bases in B6 and C6 take days. It is
helpful to be able to checkpoint progress as the algorithm progresses, so that not too much work is lost if the program
crashes, or if we need to stop it for some other reason.

Create a directory called `saves` (it can be called anything actually):

    $ mkdir saves

Now pass the `saveDir:=saves` argument to the `CalcPCanIForms` program to tell it to save its progress to that
directory. As the program runs, it will keep updating a file named something like `saves/D6-2.pcan.partial` either every
1000 basis elements or every 5 minutes, whichever comes first. The program can be killed at any time (there is no chance
of corrupting the `.partial` file). When the program is run again with the `saveDir:=saves` argument, it will load its
progress so far from the `.partial` file before continuing. When the calculation is complete, the result will be saved
into `saves/D6-2.pcan`.

For example, try the following:

    $ magma -b type:=D6 char:=2 saveDir:=saves CalcPCanIForms.m

Let it run for a few seconds, and then use `Ctrl+C` to kill it. There should now be a `saves/D6-2.pcan.partial` file.
Try running the program again using the same command line: you should get a message along the lines of

    18074 p-canonical basis elements loaded from saves/D6-2.pcan.partial

letting you know that the computation is resuming from where it left off.

Note that the partial basis files are still loadable into `IHecke` as a Literal basis, and many operations will work
with them, provided that the operations work within the defined lower-triangular part.


## Showing progress

Printing progress can be helpful during long-running computations, to make sure that the program is not frozen, and to
see where the program is spending the most time. Pass `chatty:=2` to turn up the chattiness level, and show statistics
on how long it's taking to calculate intersection forms.


# Calculations in the diagrammatic category

The code implemented here can be used to perform other calculations in the diagrammatic category. We outline a few
examples which may be instructive.


## A local intersection form

A7 is the first group in finite type A which has any kind of torsion: it has 2-torsion, and we need to go about halfway
up the group (in terms of length) in order to see it. In this example we calculate the local intersection form of a
particular Bott-Samelson object, at a particular lower element, in order to see this torsion.

First, load the package and define a category:

<!-- BEGIN TEST IntersectionForm -->

    $ magma
    > SetColumns(0);
    > AttachSpec("ASLoc.spec");
    > cartanMat := CartanMatrix("A7");
    > W := CoxeterGroup(GrpFPCox, cartanMat);
    > B := BSParabolic(CartanMatrix("A7"), W, []);

Now we define the particular Bott-Samelson object (simply a word in the generators), and the lower Coxeter group element
where we want to calculate the local intersection form.

    > bsword := [3,2,1,5,4,3,2,6,5,4,3,7,6,5];
    > w := W ! [2,3,2,5,6,5];

The function `LocalIntersectionForm` returns a triple of `(M, outexps, inexps)` where `M` is a sparse integral matrix,
`outexps` is the list of subexpressions corresponding to the rows, and `inexps` is the list of subexpressions for the
columns. The entry of the matrix is the composition `outexp . inexp`, evaluated in the truncated category with top `w`.
To just see the entries of the matrix, call `Matrix(...)` on the returned result. (Magma will not print the entries of
sparse matrices automatically).

    > Matrix(LocalIntersectionForm(B, bsword, w, 0));
    [2]

We can see that the local intersection form is a 1x1 matrix with entry 2, so A7 has 2-torsion. To see the subexpressions
used, assign all of the return values of `LocalIntersectionForm`:

    > M, outexps, inexps := LocalIntersectionForm(B, bsword, w, 0);
    > inexps[1];
    [ 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0 ]
    > outexps[1];
    [ 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0 ]

<!-- END TEST IntersectionForm -->


## Verifying relations

For how to build morphisms in the diagrammatic category, we encourage the reader to look at
[`Tests/BSCatTests.m`](Tests/BSCatTests.m), which verify some one-colour relations, and
[`Tests/Zamolodchikov.m`](Tests/Zamolodchikov.m), which verifies the Zamolodchikov relation in type A3. In particular,
vertical composition is denoted `top_diagram * bottom_diagram`, and horizontal competition denoted `cat`. The generating
morphisms are towards the end of [`Package/BSCat.m`](Package/BSCat.m).

To make it easy for users who want to check the Zamolodchikov relations in type A3 and B3 we provide three files: [`Tests/ZamolodchikovA3.m`](Tests/Tests/ZamolodchikovA3.m), [`Tests/ZamolodchikovB3.m`](Tests/ZamolodchikovB3.m) and [`Tests/ZamolodchikovA3_wrong_start.m`](Tests/ZamolodchikovA3_wrong_start.m). The first two files check the Zamalodchikov relations in type A3 and B3, and should run without error. The last one takes a different path in the reduced expression graph and should produce an error. This illustrates that the Zamolodchikov relations are sensitive to the starting point.

# Future work 

There are numerous improvements which could be made to this software, both algorithmically and from a usability
standpoint.

- (High priority) Fix up saving progress of the affine algorithm.
- Allow the calculation of p-canonical antispherical bases in the finite case, using the `CalcPCanIForms` program.
- Tidy up the internals of [`IntersectionForms`](Package/IntersectionForms.m), which was written somewhat hastily.
- The tests that validate the p-canonical results are quite old, and were set up when taking a very old version of the
  code to this one. They could be rewritten (and the IO routines could be retired?).
- Switching between various ways of representing group elements (reduced expressions, box notation, finite Weyl group
  semidirect product root lattice) is not done well, and could be greatly improved with some thinking.

# Technical notes

- There is some more technical documentation in the [old readme](./README_old.md).
- In order to run `CalcPCanIForms` fast, it is crucial that there is a fast Canonical x Canonical -> Canonical
  multiplication implemented, at least for left/right multiplication by a generator. This is the reason that IHecke
  includes [tables of mu-coefficients](https://github.com/joelgibson/IHecke/tree/main/MuCoeffs), which were calculated
  offline using a separate tool like
  [Coxeter3](http://math.univ-lyon1.fr/~ducloux/coxeter/coxeter3/english/coxeter3_e.html).
