This is a README file from an old version of the code, and may not be up-to-date.

# Overview

The inductive algorithm is contained in `ASLocNew/QPDIndec.m`, and relies only on the other files
in `ASLocNew`. Along with `QPDIndec.m`, the other core files are `StdMor.m` which implements
morphisms in the semisimple localised category, `BSMor.m` which implements the diagrammatic action
on `StdMor`, and `HeckeMod.m` which implements the antispherical module.

The code style is very "functional", meaning that most functions produce new values from their
inputs rather than modifying their inputs. In addition, most functions are written to accept
only the data they really need; for example the `GetCharacter` function which calculates the
character map (graded rank etc) takes a collection of homomorphisms as input, rather than a whole
indecomposable object. These two style choices make the code easier to follow crystal clear as to
what data is being used and where it is going. For example, it is very easy to read which functions
are characteristic-dependent and which are not.

The new code is more than 10x faster than the older code when running affine A2 with p = 3 up to
[20, 0, 0]. The biggest improvement is to the pruning light leaves step, where (a) using Magma's
native support for the Bruhat order yields improvements over using `AlcoveWeight`, and (b) the
"quotient map" is factored out so that it is computed before every loop, rather than once per loop.


# Running the code

You need to have at least Magma V2.25 installed. I am running on Magma V2.25-8.

Magma scripts can take a limited form of command-line arguments, which become available as
variables in the program. For example, running

    magma foo:=hello bar:=true baz:=[2,3] Script.m

will start the Magma program `Script.m`, with the variables `foo`, `bar`, and `baz` set to the
_strings_ `"hello"`, `"true"`, and `"[2,3]"` respectively. These strings can then be `eval`ed by
`Script.m` and used. These variables could also be created by running another script, for example

    magma Config.m Script.m

where `Config.m` assigns to the variables.

The main program is `CalcIndec.m`, which can be run as follows:

    magma type:=A~2 I:=[1,2] char:=3 target:=[20,0,0] CalcIndec.m

to perform a calculation in affine type A2, with parabolic quotient by (1, 2) in characteristic 3.
All elements less than or equal to (20, 0, 0) in the Bruhat order will be generated. Note that for
elements like `I` and `target`, spaces should not be included: use `[20,0,0]` rather than
`[20, 0, 0]` when on the command line.

A description of the options that can be passed:

- `type`, for example `type:=A~2` or `type:=C4`. Passing only this argument will print the Dynkin
    diagram, so the reader can check Magma's Dynkin diagram convention. If the type is followed by
    `rev`, for example `B3rev`, then the labelling will be reversed from Magma's default.
- `I`, for example `I=[1,3,4]`. The generating subset of the parabolic subgroup. For a maximal
    parabolic, an optimisation can be applied so that hom-spaces are over the rationals, rather
    than over a multivariate function field: the program is a lot faster in this case. Taking
    `I=[]` is allowed, and gives the p-canonical basis elements in the full Hecke algebra (but is
    hecke slow).
- `char`, for example `char:=0` or `char:=7`. The characteristic to work over.
- `target`, for example `target:=[20,20,0]` in "box-notation" or `target:=312312` in word notation.
    All indecomposables below this in the Bruhat order will be generated. May be omitted in finite
    type: it will default to the minimal coset rep of the longest word.
- `showpcan`, for example `showpcan:=true`. Show the p-canonical basis elements.
- `datadir`, for example `datadir:=data`. Will save p-canonical basis elements to the specified
    directory, in this case `data/`.
- `saveindec:=true` saves the generated indecomposable elements to the `datadir`, and also attempts
    to load them before starting. _This makes computations re-startable_.
- `profile:=prof` enables profiling, and writes the profile to `prof.html` when finished.

For example, to generate the table of 2-canonical basis elements in the full Hecke algebra ( shown
in Section 5.4 of _The p-canonical basis for Hecke algebras_ by Jensen and Williamson), run

    magma type:=B3rev I:=[] char:=2 showpcan:=true CalcIndec.m
    magma type:=C3rev I:=[] char:=2 showpcan:=true CalcIndec.m

After running, the p-canonical basis elements and indecomposable objects are stored in the
associative arrays `pcans` and `indecs` respectively. For example, after running the B3 computation
directly above, try the following in the magma terminal:

    > for k -> v in pcans do print v; end for;
    > pcans[W ! [2,3,2,1,2,3]];

If the `datadir` option was used when running `CalcIndec.m`, then the p-canonical basis elements
will be saved to some directory, say `data/type.B3.I.12.char.2/`. They can be loaded interactively:

    magma
    > AttachSpec("ASLocNew.spec");
    > W, as, pcans, ctx := LoadPcanFromDir("data/type.B3.I.12.char.2/");

`W` is the Coxeter group, `as` the antispherical module, and `pcans` an associative array of the
p-canonical basis elements. The `ctx` object contains some details on how `W` and `as` were set
up, as well as the characteristic.

# Tests

There are some ad-hoc tests such as `check-AffA2.m`, which will run the new and old code
side-by-side and check that their calculations agree _exactly_ (exactly the same matrices, for
every indecomposable object). This was useful when writing the newer code, but will become less
useful in the future when making modifications to the code which change the matrices. Most of the
tests should not rely on one or other precise basis for a hom space.

## Automated tests

There are some automated tests in the `Tests/` directory. To run the tests, change into the
directory and run

    python3 run_tests.py

All tests will be run, each either finishing in `SUCCESS` or `FAILURE`. Those that fail will be
listed with a command line for the user to run to investigate further. The tests are run in
parallel (multiple instances of Magma are started in the background) for speed. Running

    python3 run_tests.py --threads 6

for example will start up to 6 Magma instances at once (expect diminishing returns when going
beyond the number of cores in your computer's CPU).

Some of the files in `Tests/` are test _generators_, meaning that they generate data for use
in other tests. For example, the `PcanTestGenerator.m` file can be configured and then run, and
will generate the p-canonical basis using the `pDIndec` code and write it to a file. This file can
then by read in using `PcanTestRunner`, upon which the p-canonical basis in the file is compared
to the one generated by `QPDIndec`.

Automated tests are not meant to be replacements for reasoning about correct code (they should not
be relied on for correctness of code, unless a test has been written specifically to test all the
behaviour desired exhaustively). But they can be very handy for refactoring code and making sure
that everything still runs, across lots of different types and configurations.


## Writing a test

Each test is a Magma `.m` file, obeying some conventions. Each test should start with the magic
line

    if assigned batch then SetQuitOnError(true); else SetDebugOnError(true); end if;

The `run_tests.py` script will pass the argument `batch:=true` to each test, and the magic line
above tells Magma to always quit when an error is encountered in this case (rather than going
into an interactive terminal). The user can re-run the test _without_ the batch argument, then get
put into a debugger when the test errors.

Each test should also finish with `quit`, for the same reason: we want the test to never go into
an interactive terminal in batch mode.

The test itself is a normal Magma program, which throws an error if it finds something it doesn't
like. Two easy ways of throwing errors are `assert`, or `error if` for more verbose information.
For example,

    assert 2 + 2 eq 4;
    error if 2 + 2 ne 4, "Something is wrong with 2 + 2";

each do the same thing, but when run interactively the first will simply say "Assertion error",
which can be less helpful than a more informative message. A good example to read is `BSCatTests.m`
which tests whether horizontal and vertical composition is working correctly in the full localised
category.

After the test is written and functioning as intended, it can be added to the `run_tests.py` script
along with the others.


# Opportunities

There are some optimisation or simplification opportunities that we are blocked on due to missing
or slow functions in Magma. We should keep an eye on new releases of Magma for these things.

- A fast `Submatrix(::MtrxSprs, ::[RngIntElt], ::[RngIntElt])` function, we will be able to speed
    up projections to the >= x category (eg the function `QuotientIncl`) quite a bit.
- A `ChangeRing(::MtrxSprs, ::Rng, ::Map)` function, then we will be able to speed up some of the
    tensor products by a lot.
- Since `InternalTranslateLoc(M, I, J)` is equivalent to
    `KroneckerProduct(Submatrix(M, I, J), SparseIdentityMatrix(2))`, a fast `KroneckerProduct` for
    sparse matrices would allow us to remove the awkward `InternalTranslateLoc` function.
- Once more objects are understood by `WriteObject` and `ReadObject` (sparse matrices in
    particular), some of the serialisation code will be able to be simplified and sped up. But it
    does not seem to be much of a bottleneck anyway.


# Internal Magma functions

There are some functions which are undocumented (they do not appear in the handbook, but sometimes
are documented in the interpreter). These functions are _much_ faster than their Magma versions.


## InternalTranslateLoc

    InternalTranslateLoc(~X::MtrxSprs, I::SeqEnum[RngIntElt], J::SeqEnum[RngIntElt])

This is equivalent to the following psuedocode (except `X` is modified).

    KroneckerProduct(Submatrix(X, I, J), IdentityMatrixSparse(2))


## IsMinimal

    IsMinimal(I::SeqEnum[RngIntElt], x::GrpFPCoxElt) -> BoolElt

Returns whether `x` is a minimal representative in the right coset `W_I*x`.


## Echelonize

    Echelonize(~X::MtrxSprs)

Puts `X` into reduced row-echelon form, and removes the trailing zero rows. This internal function
can be used to create a fast sparse matrix inverse, and is also used to decompose a sparse
idempotent into a projection and inclusion.


# Serialisation

The older code can generate indecomposables up to (20, 0, 0) in type affine A2 for p = 3, and save
them as it runs. It takes 200 seconds to generate 122 MB of data, and when started again it can
read that data back into indecomposables in about 1.2 seconds. The data written are the p-canonical
basis elements, stored in files which can be `load`ed or `eval`ed back into Magma, and the
morphisms which are more complicated. Each morphism is written to a different file using the
`WriteSparseMatrix` function, and read back using the `ReadSparseMatrix` function. The file name
determines where the morphism "goes", for example the file `X_Y_LLin2.dat` would mean the second
morphism in the hom space `LLsIn[Y]` on the indecomposable `X`.

The newer code takes a different approach. Magma has recently acquired `WriteObject` and
`ReadObject` functions, which are intended to be used to send objects over sockets (for distributed
computing, or communicating with other programs). Objects written in this way can be very quickly
written and read, but not all object types are supported. Importantly for us, sparse matrices,
Coxeter group elements, associative arrays, and Laurent series are not supported, and neither are
user-defined objects. We get around this by defining a "serialisation" of an indecomposable into
a simpler Magma data structure which `WriteObject` understands. For example:

- A Coxeter group element can be turned into its word (a sequence of integers) using `Eltseq`, and
    converted back using `W ! word`.
- An element of the Hecke algebra can be scaled by the lowest power of `v` appearing, and converted
    to a pair of (polynomial, lowest power), allowing us to encode coefficients since `WriteObject`
    understands polynomials.
- A sparse matrix can be converted into (number of rows, number of columns, entries) where the
    entries are the `Eltseq` of the sparse matrix, a list of `<i, j, A[i, j]>` for all `i` and `j`
    in the support of the sparse matrix.

The whole indecomposable can then be turned into a record and back again. (A few other tricks are
used to take advantage of repeated information in order to condense the size of the record). The
record can then be written to a file, sent over a socket, or whatever. A significant benefit of
this approach is that it is easy to test whether serialisation and deserialisation works, without
needing to touch any files: we can then rely on the correctness of `WriteObject` and `ReadObject`
for actually reading and writing the records to files. Also, we can store a bit of "contextual
data" (Cartan matrix, characteristic, etc) along with each indecomposable, so that we have a bit
of error checking against reading the wrong file, and the ability to interpret each file out of
context.

Using this approach, doing the same calculation as above up to (20, 0, 0) in affine A2 for p=3
with QPDIndec generates 26 MB of data in 50 seconds, and can read all the data back in 1.6
seconds. It appears that by using compression (`gzip` or `xz` on their default settings), we
can reduce the data size by 1/2 or 2/3, so this could be an option in the future.

One caveat of this approach is that the internal format used by `WriteObject` and `ReadObject` may
change with different versions of Magma. It is designed to be backwards-compatible however, so that
two different version of Magma can first communicate their protocol numbers, then start exchanging
objects. If this becomes a problem, we could solve it by just prepending each file with the
protocol number.


# Parallelisation / Distributed computation

A first approach to parallelising the code is to start multiple worker processes and have them all
connect to a single manager process. The manager will do no computation of indecomposables, instead
it will just keep every worker updated with the full list of indecomposables calculated thus far,
determine which indecomposable objects are ready to be calculated, and tell each worker what to
calculuate.

Sending the full list of indecomposables is simple, but incurs a large communication overhead which
scales linearly as the number of workers increases, slowing down the overall algorithm. It also
makes RAM usage scale linearly with the number of workers, which is inconvenient on non-server
computers. A better approach would be to only send "skeleton" data for every indecomposable to
every worker ("skeleton" data being the `canPol`, `stdSeq`, and inclusions and projections), since
this is the only global data needed: after that, the indecomposable for x can be produced from the
hom spaces of its immediate right descents.

Currently, the manager process and worker processes can be started like

    magma char:=2 type:=A~2 targetParam:=[20,0,0] affroot:=3 CalculateManager.m

    # Start in one or more other terminals
    magma host:=localhost port:=2222 CalculateWorker.m


# Working over finite fields

Time taken to calculate all the p-canonical basis elements for C4, p = 2 using the finite field method:

    $ time magma -b type:=C4 I:=[] char:=2 showpcan:=true CalcIndecFp.m
    Executed in   37.05 mins   fish           external
        usr time   36.96 mins  285.00 micros   36.96 mins
        sys time    0.06 mins   55.00 micros    0.06 mins

The other mode did not finish even with 265 mins (7x running time at least).


# TODO

- At the moment we are taking the tensor product of morphisms, but perhaps it would be more efficient
    to implement the tensor products (object x morphism) and (morphism x object), then use composition.
- (Done) Faster generation of subsequences evaluating to a certain word.
- (Done) Inverse symmetry.
- (Low priority) Make the Bott-Samelson category not need the framing Coxeter elements on every point in the localised
    domain and codomain, since it is very expensive to keep calculating these. Instead a BSMor should
    store source and target expressions in the simple generators, a bare localised matrix, and we
    expand the framing elements when acting on the standard category.
    Though this doesn't seem to be as much of a problem as I thought for F4.
    (This would shave off about 5% in the D6, p=2 example, so perhaps not worth it so much)
- (High priority) The big time sink is the braid moves: eg when calculating the first 700 elements of F4, 20 out
    of 30 of the seconds spent in generating light leaves down is taken up simply by multiplying
    a braid with a light leaf, and a further 5 seconds is spent generating those braids. It looks
    like my braiding strategy might be suboptimal here, for example forcing words to end in a
    braid might be causing bad behaviour later (it also seems that applying an m_st=4 braid move
    at the end of a light leaf is very expensive). I should try different ways of making a light
    leaf end with a certain letter.
    In D6, p=2, these braid moves are taking 95% of the time of light leaf construction. Of this, it seems that 3% is taken by actually constructing the braid morphism, and 97% of the time is multiplying that braid onto the light leaf which is being built.
    So these multiplications are the single most expensive part of the whole algorithm.
- Can cut down time to generate Bott-Samelson basis elements by memoising (Magma seems to use a
    normal form where every prefix of a normal form is again a normal form).
- Make an actual log of p-canonical bases which we (or Thorge) have computed.

# Other ideas

The star operations, Schutzenberger involutions, and this recent paper with Ben and Thorge seem
to all have some link to the Cactus action, as explained in Cells and Cacti. Cells and Cacti also
goes into the mixed basis. I think there could be something to take away from there, and perhaps
we could get more symmetries of the p-canonical basis.

Another thing we could do is proceed in chunks, rather than one by one. I need to think about this
further, but potentially there might be relations amongst elements of the same length, and so data
about one might inform the other enough to avoid an intersection form calculation.

To decide whether to subtract a multiple or not, we usually need to calculate an intersection form.
We could pre-emptively subtract a multiple and see if any negative coefficients pop out, which would
give a contradiction, but actually implementing this idea seems to do nothing. (I suppose that
Bott-Samelson objects are "too big" for this to work). Is there something special we could do with
p-canonical basis elements which are equal to their canonical basis elements?

Should do antispherical objects.

It seems (should check this with a profiler) that after the large speedup, the most expensive operation
is actually calculating the gram matrix of the vectors coming out of the light leaves. Perhaps we should
explore whether each of the ins and outs vectors span lower-dimensional subspace, so as to reduce the size
of the matrix product which is being taken. Should also investigate whether actually encoding the vectors
as sparse matrices and using the sparse matrix product speeds things up.

Use the diagram symmetry in types An, Dn, and E6.


# Progress

Documenting how things improved.

- The first 700 elements of F4 p=2: 750 intersection forms calculated in 400 seconds (profiler on).
- After using left and right star operations, only need 293 intersection forms: 146 seconds.
- Inverse symmetry: 176 intersection forms calculated, 78 seconds with no profiler.
- Added finer degree bounding, 164 intersection forms calculated, 70 seconds with no profiler


# Magma performance notes

- For creating a Coxeter group element, coercion like `W ! [s : ...]` is much faster than `&*[W.s : ...]`.
- `Eltseq` on sparse matrices is quite expensive to call repeatedly, it is better to use `Support(M, i)` etc to iterate directly.
