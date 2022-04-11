#!/usr/bin/env python3

import argparse
import multiprocessing.dummy # Uses threads
import subprocess
import time

# Put the word "magma" in front of each of these to run.
TESTS = [
    # Short and fast tests first.
    "Tests/StdCatTests.m",
    "Tests/BSCatTests.m",
    "Tests/BoxTestA2.m",
    "Tests/BoxTestC2.m",
    "Tests/Zamolodchikov.m",

    # Check that saving and loading from files works correctly.
    "type:=A~2 param:=[0,30,0] affroot:=3 checkserialise:=true Tests/CanTestRunner.m",

    # Short consistency checks, to check that for p=0 we get the canonical basis.
    "type:=A~2 param:=[0,30,0] affroot:=3 Tests/CanTestRunner.m",
    "type:=C~2 param:=[0,20,0] affroot:=3 Tests/CanTestRunner.m",

    # Check the main programs are not crashing.
    "type:=A~2 I:=[1,2] char:=3 target:=[5,5,0] CalcIndec.m",
    "type:=B4 char:=2 CalcPCanIForms.m",

    # Longer tests, using tables of p-canonical basis elements.
    "filename:=Tests/pcan-A~2-3-upto-20-0-0 limit:=300 Tests/PcanTestRunner.m",
    "filename:=Tests/pcan-A~2-5-upto-30-0-0 limit:=300 Tests/PcanTestRunner.m",
    "filename:=Tests/pcan-C~2-5-upto-0-15-0 limit:=0 Tests/PcanTestRunner.m",
    "filename:=Tests/pcan-C~2-17-upto-0-50-0 limit:=400 Tests/PcanTestRunner.m",
    "filename:=Tests/pcan-G~2-11-upto-0-10-0 limit:=150 Tests/PcanTestRunner.m",
]

def run_test(test):
    cmd = ['magma', '-b', 'batch:=true'] + test.split()
    start_time = time.time()
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    return_code = proc.wait()
    finish_time = time.time()

    # As of Magma V2.26-8, the error code is sometimes 0 even when there was an error.
    if b'error' in proc.stdout.read().lower():
        return_code = 1

    return test, cmd, return_code, finish_time - start_time

def run_tests_parallel(tests, nthreads):
    print(f"Running {len(tests)} tests, up to {nthreads} simultaneously.")
    print()

    pool = multiprocessing.dummy.Pool(nthreads)
    failures = []
    for test, cmd, return_code, elapsed in pool.imap_unordered(run_test, tests):
        if return_code == 0:
            print(f"SUCCESS: {' '.join(cmd)}")
        else:
            print(f"FAILED:  {' '.join(cmd)}")
            failures += [test]

        print(f"   Elapsed time: {elapsed : .2f} seconds.")
        print()

    if failures:
        print(f"{len(failures)} out of {len(tests)} tests failed. Run their commands for more details:")
        for test in failures:
            print(f"   magma {test}")
    else:
        print(f"All {len(tests)} tests passed")


parser = argparse.ArgumentParser(description="Run tests for QPDIndec.")
parser.add_argument('--threads', type=int, default=4)
args = parser.parse_args()

run_tests_parallel(TESTS, args.threads)
