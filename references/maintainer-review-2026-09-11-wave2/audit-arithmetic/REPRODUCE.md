# PR89 review reproduction

Source head reviewed: `3443179cb62b410678f3c67f26cd8df56ba6133a`.
The report covers exact certificate verification, not regeneration of heuristic
searches. Use an isolated checkout of that head. Required: Python 3.10+, a C++17
compiler supporting unsigned 128-bit integers, and Boost multiprecision headers.
The actual review used Apple Clang 21, Python 3 and Boost 1.88.0. Boost's official
source archive SHA256 was
`46d9d2c06637b219270877c9e16155cbd015b6dc84349af064c088e9b5b12f7b`.

Run from the isolated repository checkout, with the following paths set to your
local review output and Boost headers. The output directory must differ from
the submitted package directory.

```sh
REVIEW_PACKAGE="$PWD/references/colbrook-arithmetic-2026-09-11/submitted/NLA_partial_results_submission_package"
REVIEW_OUT="/private/tmp/pr89-exact-rerun"
BOOST_INCLUDE_DIR="/path/to/boost_1_88_0"
mkdir -p "$REVIEW_OUT/build"
clang++ -O3 -std=c++17 -pthread -I"$BOOST_INCLUDE_DIR" "$REVIEW_PACKAGE/src/verify_permanent.cpp" -o "$REVIEW_OUT/build/verify_permanent"
clang++ -O3 -std=c++17 "$REVIEW_PACKAGE/src/check_range.cpp" -o "$REVIEW_OUT/build/check_range"
```

Run every required complete matrix and every unrestricted inclusion, preserving
outputs and requiring success. The largest full-matrix job uses four threads;
the range check is single-threaded. These are finite exact searches, not samples.

```sh
python3 - "$REVIEW_PACKAGE" "$REVIEW_OUT" <<'PY'
from pathlib import Path
import subprocess,sys
package,out=map(Path,sys.argv[1:])
with (out/'full-matrix-checks.log').open('w') as f:
    for n in range(1,36):
        subprocess.run([str(out/'build/verify_permanent'),str(package/f'data/ac11/min{n}.txt'),'4'],stdout=f,stderr=f,check=True)
        f.flush()
with (out/'range-checks.log').open('w') as f:
    for n in range(1,11):
        subprocess.run([str(out/'build/check_range'),str(n),str(package/f'data/ac12/u{n}_spectrum.txt'),str(out/f'range{n}')],stdout=f,stderr=f,check=True)
        f.flush()
PY
```

Use the fresh independent Python script from this review with explicit paths:

```sh
python3 /path/to/independent_permanent_checks.py --package "$REVIEW_PACKAGE" --verifier "$REVIEW_OUT/build/verify_permanent" --out "$REVIEW_OUT"
```

It independently recomputes all 5,528 witness records by exact Ryser
inclusion-exclusion, enumerates every normalized matrix through order 5 without
the submitted symmetry/pruning code, crosschecks direct permutations, checks
signed cases and deliberately wrong claims, and writes structured JSON results.
It does not import submitted Python code.

To reproduce the submitted DP/test harness as a separate corroboration, copy
its inspected inputs into scratch and point its expected build directory at the
independently rebuilt verification binaries:

```sh
python3 - "$REVIEW_PACKAGE" "$REVIEW_OUT" <<'PY'
from pathlib import Path
import shutil,subprocess,sys
package,out=map(Path,sys.argv[1:]);work=out/'test-package';work.mkdir()
for name in ('tools','tests','data'):
    shutil.copytree(package/name,work/name)
shutil.copy2(package/'claims.json',work/'claims.json')
(work/'build').symlink_to((out/'build').resolve(),target_is_directory=True)
with (out/'submitted-data-tests.log').open('w') as f:
    subprocess.run([sys.executable,str(work/'tests/check_data.py')],stdout=f,stderr=f,check=True)
PY
```

`pdf-qa/report.json` and `pdf-source-rebuild-results.json` record the read-only
PDF QA. The local review rendered all 27 pages of the five final PDFs, inspected
every page, and rebuilt unchanged TeX sources twice using XeLaTeX with
`-no-shell-escape`. All extracted text matched exactly; the report describes the
single negligible spacing variation. Retained historical PDFs and missing
AA-01 experimental programs are outside this final-document/software rerun.
