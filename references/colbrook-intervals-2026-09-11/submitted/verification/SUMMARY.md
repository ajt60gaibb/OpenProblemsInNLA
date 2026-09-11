# Retained verification record

These are finite regression checks, not proofs. Exact and floating-point runs are distinguished. Missing or interrupted runs are not counted as passes.

| Result file | Arithmetic | Retained status |
|---|---|---|
| `AV-01_exact_results.json` | exact Fraction and SymPy rational | **passed** |
| `exact_results.json` | Exact integers, fractions, and SymPy rationals | **passed** |
| `av01_numeric_results.json` | floating point; diagnostic only | **passed** |
| `iv03_numeric_results.json` | floating point; diagnostic only | **passed** |
| `iv05_numeric_results.json` | Not recorded | Not present |

## Recorded details

### AV-01_exact_results.json

```json
{
  "started_utc": "2026-09-11T14:10:50.807936+00:00",
  "arithmetic": "exact Fraction and SymPy rational",
  "checker": "Fourier--Motzkin feasibility versus all orthants",
  "checker_is_not_a_polynomial_LP_implementation": true,
  "status": "passed",
  "instances": 1046,
  "dimensions": {
    "1": 45,
    "2": 701,
    "3": 300
  },
  "accepted": 154,
  "elapsed_seconds": 0.8545963149999807,
  "finished_utc": "2026-09-11T14:10:51.662648+00:00"
}
```

### exact_results.json

```json
{
  "started_utc": "2026-09-11T14:32:47.723481+00:00",
  "mode": "full",
  "arithmetic": "Exact integers, fractions, and SymPy rationals",
  "finite_tests_are_not_a_proof": true,
  "IV-06": {
    "status": "passed",
    "integer_eigenpairs": 4,
    "excluded_separators": [
      {
        "lambda": -1,
        "determinant_interval": [
          -332,
          -32
        ]
      },
      {
        "lambda": 1,
        "determinant_interval": [
          -318,
          -18
        ]
      },
      {
        "lambda": 12,
        "determinant_interval": [
          -3750,
          -150
        ]
      }
    ]
  },
  "IV-02_IV-04": {
    "status": "passed",
    "partition_instances": 430,
    "exact_gate_vertices": 15303,
    "matrix_and_cofactor_checks": 15
  },
  "AV-02": {
    "status": "passed",
    "graphs": 160,
    "integer_gap_checks": 1070,
    "exact_block_inverse_checks": 14,
    "exact_NP_certificates": 14
  },
  "IV-03": {
    "status": "passed",
    "rational_boxes": 1356,
    "entry_vertices_checked": 2325,
    "all_2x2_endpoint_boxes_in_0_1_2": 1296
  },
  "IV-05": {
    "status": "passed",
    "rational_boxes": 60,
    "exact_primal_dual_LP_certificates": 300,
    "exhaustive_matrix_vertices": 820
  },
  "status": "passed",
  "elapsed_seconds": 5.655857927999932,
  "finished_utc": "2026-09-11T14:32:53.379364+00:00"
}
```

### av01_numeric_results.json

```json
{
  "started_utc": "2026-09-11T14:14:19.239018+00:00",
  "arithmetic": "floating point; diagnostic only",
  "section": "av01",
  "mode": "full",
  "instances": 9200,
  "accepted_by_dimension": {
    "1": 160,
    "2": 619,
    "3": 466,
    "4": 131,
    "5": 22,
    "6": 1,
    "7": 0,
    "8": 0
  },
  "mismatches": 0,
  "status": "passed",
  "elapsed_seconds": 17.777854269000045,
  "finished_utc": "2026-09-11T14:14:37.016893+00:00"
}
```

### iv03_numeric_results.json

```json
{
  "started_utc": "2026-09-11T14:22:55.333533+00:00",
  "arithmetic": "floating point; diagnostic only",
  "section": "iv03",
  "mode": "full",
  "boxes": 1000,
  "vertices_checked": 399500,
  "accepted_by_dimension": {
    "2": 102,
    "3": 156,
    "4": 81,
    "5": 70,
    "6": 50,
    "7": 28
  },
  "mismatches": 0,
  "status": "passed",
  "elapsed_seconds": 12.142768696000076,
  "finished_utc": "2026-09-11T14:23:07.476324+00:00"
}
```

## Build audit

The reader contains 19 pages. Individual PDF page counts and LaTeX warnings are recorded in `metadata/package_build.json`. Page rendering and automated bounds checks are reported there separately from mathematical tests. No independent visual or mathematical reviewer is asserted.

## Exploratory work

IV-01 search files, when present, are exploratory. A search with no counterexample is not a proof; a machine-generated candidate requires a separate audit. AV-03 and IV-01 remain outside the seven claimed resolutions.
