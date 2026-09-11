# Exact finite cases for AC-11 and AC-12

**These are finite-case certificates, not complete all-orders solutions. No repository issue has been posted or closed.**

## Certified results

For **AC-11**, the data give a sign matrix of every order **1 through 35** attaining

`q(n) = 2^(n - floor(log2(n+1)))`.

The proved universal divisibility bound then identifies the least positive permanent at each of these orders. There are **15 explicitly certified orders from 21 through 35**, beyond the order-20 construction range in the cited Wanless paper. This comparison is **not a claim of literature priority**. Every complete matrix is checked without trusting the accompanying cofactor vector.

For **AC-12**, the data and inclusion checks certify the entire common permanent range for **every order 1 through 10**. The restricted family consists of sign matrices with **+1 below the diagonal**, not ordinary upper triangular matrices. Negative diagonal entries are allowed.

| Order | Absolute values | Signed values |
|---:|---:|---:|
| 1 | 1 | 2 |
| 2 | 2 | 3 |
| 3 | 2 | 4 |
| 4 | 5 | 9 |
| 5 | 8 | 15 |
| 6 | 16 | 31 |
| 7 | 36 | 72 |
| 8 | 158 | 315 |
| 9 | 506 | 1,011 |
| 10 | 1,933 | 3,865 |

The range certificate has two indispensable parts: exact evaluation of every explicit restricted-family witness, and exhaustive inclusion of the unrestricted range in the witnessed set. The latter uses representative coverage and a proved prefix-completion bound. Sampling is only a witness-finding device, never a completeness argument. The `o9` and any higher `o` catalogues reuse the restricted witnesses as unrestricted membership witnesses; their completeness comes from the bound checker, not from an unfinished unpruned enumeration.

## Main files

`manuscript.pdf` is the self-contained mathematical note. `manuscript.tex` and its generated table fragments are the editable source. `claims.json` records the exact finite scope. `data/ac11` contains full matrices, scaled cofactor vectors, and generation parameters; `data/ac12` contains exact ranges and explicit witnesses. `src` contains the search, complete-matrix verifier, range enumerator, range-inclusion checker, and a bordering witness generator. `tests` and `tools` provide arbitrary-precision checks and a constructive restricted-realization utility. `submission` contains two issue drafts and a cover note. Retained evidence is in `logs`; `SHA256SUMS` lists the delivered file digests.

## Reproduce the certificates

Requirements are a C++17 compiler with `unsigned __int128` support (GCC or Clang), Boost multiprecision headers, Python 3.10 or later, and Bash. The Python checks use only the standard library. TeX is needed only to rebuild the note, not to check the mathematics.

```sh
./reproduce.sh
```

This builds the tools, checks every range witness using arbitrary-precision subset dynamic programming, verifies every complete AC-11 matrix using two coprime moduli and a proved uniqueness bound, and checks unrestricted range inclusion at each certified order. It stops on failure and writes fresh logs under `rerun/`. The default uses one verification thread; individual full-matrix checks also accept a thread count. Runtime depends on hardware and order; the included observations are not performance guarantees.

For a single complete matrix:

```sh
./build.sh
build/verify_permanent data/ac11/min35.txt 2
```

For a single range certificate, **both** commands are needed: witness membership must not be omitted.

```sh
python3 tests/check_data.py
mkdir -p rerun
build/check_range 10 data/ac12/u10_spectrum.txt rerun/range10
```

A cofactor dot-product match is not, by itself, a full permanent verification. An inclusion check against a set without verified witnesses is not, by itself, a range equality proof. The main reproduction script performs the missing checks in both cases.

## Construct a restricted realization

For an input sign matrix of a certified range order, this utility computes its exact permanent, looks up a restricted witness, and fixes its sign by changing the first row when necessary:

```sh
python3 tools/realize.py data/ac11/min8.txt rerun/realized8.txt
build/verify_permanent rerun/realized8.txt
```

The input format is a line containing `n claimed_permanent`, followed by `n` rows of `n` entries in `{-1, +1}`. The realization utility ignores the input claim and recomputes the permanent. It rejects uncertified orders.

## Regeneration and independent checks

The base matrix generation is deterministic for the recorded seed and attempt. Equal signed sums can select different valid last rows across standard-library sorting implementations; byte-identical regeneration is not required for a certificate. For example, order 32 used the fourth base matrix:

```sh
mkdir -p rerun
build/find_min 32 20260911 rerun/min32 1 3 glynn
build/verify_permanent rerun/min32.txt
```

The arguments after the output prefix are the number of attempts, the number of preceding attempts to skip, and the cofactor method. Generation is optional for certificate verification. The independent subset-DP cofactor method can be selected as `dp`; it was used to cross-check orders 21–28. Its memory cost is exponential, so the default reproduction script does not allocate those large DP tables.

The normalized restricted and unrestricted representative enumerations through order 8 are also reproducible with `build/spectrum`. The complete upper-family run at order 8 examines 17,179,869,184 normalized matrices; the faster witness-plus-inclusion certificate avoids requiring that run from a reviewer.

The note can be regenerated with a standard LaTeX installation:

```sh
python3 tools/build_note.py
pdflatex -interaction=nonstopmode -halt-on-error manuscript.tex
pdflatex -interaction=nonstopmode -halt-on-error manuscript.tex
```

## Submission status and references

The issue drafts follow the repository's correction/result template. AC-11 should remain partially resolved. The AC-12 draft presents finite special cases and asks the maintainer to decide whether those warrant “Partially resolved”; it explicitly does not ask for closure as solved. Authorship, independent review, an archival reference, and literature-priority checking remain matters for the person submitting the package. See `PROVENANCE.md` and `RESEARCH_STATUS.md`.

Primary references are I. M. Wanless, *Permanents of matrices of signed ones*, Linear and Multilinear Algebra 53(6) (2005), 427–433, §3, pp. 430–431, DOI 10.1080/03081080500093990; and DeVon Ingram and Alexander Razborov, *On the Range of the Permanent of (±1)-Matrices*, arXiv:2507.09433, §6, Problems 3–4. The repository's AC-11/AC-12 statements and contribution guidance were consulted on 11 September 2026. Full linked references appear in the note and issue drafts.

## Retained verification evidence

`logs/final_full_matrix_checks.log` covers all 35 minimum-permanent matrices, and `logs/final_range_checks.log` covers the 10 range-inclusion checks. These files explicitly combine separately completed runs. `logs/data_tests.log` records the independent witness, small-matrix, and negative tests. `logs/cofactor_dp_comparison.log` records the separate cofactor recurrence comparisons for orders 21–28.

`SHA256SUMS` covers the supplied source, data, note, drafts, and retained logs. On a system with `sha256sum`, run `sha256sum -c SHA256SUMS` before reproduction to check file integrity. Checksums do not replace the mathematical checks.
