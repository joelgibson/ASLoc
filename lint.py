"""
Some code quality checks.
"""

import glob


SOURCE_FILES = [
    *glob.glob("Package/*.m"),
    *glob.glob("Tests/*.m"),
    *glob.glob("*.m"),
]

def check_file(fname: str):
    for line_no, line in enumerate(open(fname), start=1):
        line = line.rstrip('\n')

        if '\t' in line:
            print(f"{fname}:{line_no} tab in line")

        if line.rstrip() != line:
            print(f"{fname}:{line_no} trailing space")

        if 'todo' in line.lower():
            print(f"{fname}:{line_no} TODO found: {line}")


for fname in SOURCE_FILES:
    check_file(fname)
