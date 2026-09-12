# How to use this proof pack

Start with `MANIFEST.md`, then each problem's `result.md` and `self_review.md`.
All mathematical content is editable Markdown. Exact data use JSON strings
for rational numbers, never decimal approximations.

## Reproduction

Run `python verify_pack.py` from this directory. Python 3.10 or newer is needed
for the type annotations used by the scripts; the audit was run with Python
3.13.5. Only the standard library is required. Do not run with `python -O`,
because the regression scripts intentionally use assertions.

The verification command runs the two AVE solver suites, exact obstruction
checks, cyclic handicap checks, reconstruction of the IV example, and an
independent determinant/graph audit. Tests write their JSON logs next to their
scripts. Wall-clock timing fields in regenerated logs will naturally differ.

## Main supporting files

| Directory | Files | Purpose |
|---|---|---|
| AV-03 | `hessenberg_solver.py`, `test_solver.py`, `test_results.json` | Theorem H implementation and 108 exact cases. |
| AV-03 | `feedback_solver.py`, `test_feedback.py`, `feedback_test_results.json` | Theorem F implementation and 84 exact cases. |
| AV-03 | `verify_obstructions.py`, `obstruction_certificates.json` | Exact Newton and inverse-hull witnesses, and all tent itineraries in the recorded finite dimensions. |
| AV-03 | `verify_handicap.py`, `handicap_test_results.json` | 10,116 rational margin checks and sharp/scaled witnesses for the separately proved handicap formula. |
| IV-01 | `minor_tools.py`, `build_and_verify_example.py`, `mixed_parity_example.json` | Exact boundary construction and its complete rational data. |
| IV-01 | `A_minus_all_minors.json`, `A_plus_all_minors.json` | Every endpoint minor, its row/column index set, and signed determinant. |
| IV-01 | `graph_criterion.py`, `scc_reduction.py` | Sufficient-condition and cycle-normal-form certificates, not general SR decision procedures. |
| IV-01 | `test_graph_and_certificates.py`, `independent_audit_results.json` | Independent Leibniz checks of all 1255 certified minor values and six graph edge-case checks. |
| IV-01 | `build_both_boundary_example.py`, `both_boundary_example.json`, `A_both_boundary_all_minors.json`, `B_both_boundary_all_minors.json` | Stronger example with zero middle minors at both endpoints. |
| IV-01 | `order_two_reduction.md`, `verify_order_two.py`, `order_two_test_results.json` | General order-two reduction and finite exhaustive binary regression. |
| IV-01 | `dimension_five_theorem.md`, `verify_dimension_five.py`, `cyclic_graph_dimension_five_example.json` | Stronger n=5 theorem and a cyclic fixed-graph example with both endpoints non-strict. |
| source_notes | `SOURCES.md` | Canonical scope, blob identifiers, source verification, and ordering. |

The root `SHA256SUMS` records the delivered bytes. Rerunning a script changes
its timing-bearing outputs and therefore changes their hashes; this does not
indicate a mathematical discrepancy.

## Research record

The recorded research window began on 2026-09-12 at 17:03:53 UTC. Work proceeded
through AV-03, then IV-01, and returned to AV-03 for extensions and the handicap
calculation. The final record in `verification_summary.json` gives the final
verification time. These are wall-clock records, not measured CPU time or a
claim that computations ran asynchronously. Exact certificate computations
were rerun in the final runtime before packaging. Earlier discovery-only
observations are not required for any theorem in the delivered files.

## Optional exploration of the remaining dimension-five gap

These two completed searches are separate from the theorem regression suite:

```sh
python IV-01/search_fixed_singular_block.py --restarts 8 --steps 6 --vertices 128 --seed 20260912
python IV-01/search_fixed_singular_block.py --restarts 4 --steps 6 --vertices 256 --seed 20260914
```

They preserve a fully fixed singular adjacent 2 by 2 block and use exact
arithmetic to seek a wrong-sign order-three minor. Their logs are included.
They found no witness, which is not an exhaustive result or a proof.
