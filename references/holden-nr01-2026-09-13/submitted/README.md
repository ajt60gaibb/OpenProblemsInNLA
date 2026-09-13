# NR-01: exact ranks for the regular 17-, 18-, 19-, and 20-gons

## Result and scope

This package gives a computer-assisted proof draft of

    rank_+(S_n) = 9 for n = 17, 18, 19, 20,

where S_n(i,j) = cos(pi/n) - cos((2i+1-2j)pi/n).

It closes the n=17 gap left by the preceding package. It does **not** prove the
conjectured formula for every n. The first unresolved size under the results
assembled here is n=25, with 9 <= rank_+(S_25) <= 10. There is no claim of external
peer review, proof-assistant formalization, or a complete priority search.

Start with **report/NR01_round2.pdf**. Its editable LaTeX source is included.
The previous rank-balance archive is retained unchanged under `prior_round/`.
Its former statement that n=17 is unresolved is superseded by this report.

## Proof structure

A rank-eight factorization would give a bounded four-dimensional polytope with
exactly eight facets projecting onto the regular polygon. The proof regenerates
a complete catalogue of the 39 simplicial 3-spheres on eight vertices, using the
published classification count for completeness. It then exhausts 14,837,760
projected-normal order/sign configurations for the 23 eligible types.

The generic shadow cover contains 855 distinct 17-cycles, 192 distinct 18-cycles,
and 14 distinct 19-cycles, but no 20-cycle. A limiting argument handles nonsimple
lifts and nongeneric projections. It produces 6,147 selected patterns for n=17,
449 for n=18, and 14 for n=19.

For each selected pattern, determinant constraints give a linear system in the
bivector of the two extra lift coordinates. Plucker quadratics impose its
decomposability. Exact modular rank tests prove that the only possible nonzero
decomposable directions are complementary-pair directions; these would force
n-2 exposed lift points into a plane section having at most eight vertices.
This is a contradiction. A separate shadow-capacity argument excludes n=20.

The finite-field calculations certify nonzero minors and hence rank lower
bounds over the cyclotomic number field. They do **not** infer real
infeasibility merely from the absence of finite-field points. Hypothetical
factorizations may have arbitrary real entries; no algebraicity assumption is
imposed on their coordinates.

## Reproduce the checks

Tested with Python 3.13.5, NumPy 2.3.5, Numba 0.65.1, and SymPy 1.14.0.
The dependency versions are pinned in `requirements.txt`.

From this directory:

```sh
python -m pip install -r requirements.txt
python code/verify_all.py
python code/test_pipeline.py
```

Installation may require network access. Verification itself is offline and
uses no optimization solver, floating-point infeasibility tolerance, or remote
service. The main proof decisions use exact integer or prime-field arithmetic.
The optional floating-point evaluators inherited in `regular_polygon.py` are
not used to certify the theorem.

The full verifier runs each stage in a separate Python process and writes new outputs to `checks/latest/` and compares the
regenerated combinatorial data with the frozen data. It does not overwrite
`checks/release/` unless that path is supplied explicitly. Avoid
`--refresh-data` for a normal audit: that option deliberately replaces frozen
data rather than comparing them.

For resource-limited execution, the same verification can be run in separate
stages, as it was for the supplied release outputs:

```sh
python code/verify_all.py --stage geometry
python code/verify_all.py --stage algebra --n 17 --prime 103
python code/verify_all.py --stage algebra --n 17 --prime 137
python code/verify_all.py --stage algebra --n 18 --prime 109
python code/verify_all.py --stage algebra --n 18 --prime 163
python code/verify_all.py --stage algebra --n 19 --prime 191
python code/verify_all.py --stage algebra --n 19 --prime 229
python code/verify_all.py --stage upper
python code/verify_all.py --stage summary
python code/test_pipeline.py
```

The **summary-only** stage validates the completeness and consistency of saved
outputs; it does not rerun the arithmetic. A complete audit requires the
preceding computational stages as well.

## Release results

| n | Distinct selected patterns | First prime | Second prime | Excluded in both passes |
|---|---:|---:|---:|---:|
| 17 | 6,147 | 103 | 137 | 6,147 |
| 18 | 449 | 109 | 163 | 449 |
| 19 | 14 | 191 | 229 | 14 |

There are 13,220 successful pattern-prime checks. The second pass changes the
prime, the coordinate gauge, and the determinant subset. In 18 n=17 patterns,
the linear kernel has an extra direction that is removed by the quadratic
calculation. All other patterns have linear nullity equal to the number of
known complementary-pair directions.

A known feasible eight-term factorization for the regular 16-gon is correctly
**not excluded** by the same test. All four stored nine-term upper
factorizations pass exact entrywise verification. Additional checks cover 28
matrices in total (n=3..24 and n=43..48), with 17,334 exact entry identities.
All 13 regression tests pass, including independent arithmetic comparisons and
rejection of a deliberately corrupted factorization.

## File guide

- `report/`: mathematical report in PDF and LaTeX.
- `code/geometry.py`: sphere generation, generic shadow enumeration, and the
  degeneration-safe selected-pattern cover.
- `code/algebra.py`: exact modular incidence and Plucker tests.
- `code/verify_all.py`: full or staged reproduction driver.
- `code/test_pipeline.py`: thirteen regression tests.
- `code/regular_polygon.py`, `code/verify_exact.py`: retained exact upper
  construction and integer-polynomial certificate verifier.
- `data/`: frozen sphere catalogue, shadow cycles, selected patterns, and four
  explicit upper factorizations. Facet sets are eight-bit integer masks.
- `checks/release/`: every per-pattern rank record and the aggregate summary.
- `checks/*.log`: successful staged release runs and regression output.
- `prior_round/`: the preceding archive, byte-for-byte unchanged.
- `sources.json`: primary references and the precise role of each source.
- `STATUS.md`: claims, limitations, and the first remaining mathematical gap.
- `MANIFEST.sha256`: hashes of the released files other than the manifest itself.

To rebuild the PDF, install a LaTeX distribution with the packages named in its
preamble, then run `sh build_report.sh`. The PDF is already supplied, so LaTeX is
not required for the algebraic or combinatorial checks.

The central audit obligations are the generic-to-degenerate reduction and the
characteristic-zero specialization lemma. Successful arithmetic checks do not
replace those proofs. The finite catalogue depends explicitly on the published
39-sphere classification; that external theorem is not reproved here.
