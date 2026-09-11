# Scope and status

**Complete all-orders resolutions produced: zero.** The certified contributions concern finite parameter ranges of AC-11 and AC-12. Their exact scope is recorded in `claims.json`. Neither issue draft asks to mark an all-orders conjecture solved.

The [arithmetic-and-complexity section](https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/arithmetic-and-complexity) was inspected as a 14-problem collection. Detailed exact computation concentrated on the two permanent questions. No verified new result is submitted for the other twelve entries.

| Entry | Target | Result produced here |
|---|---|---|
| AA-01 | Decidability of accurate polynomial evaluation | No decision procedure with a full correctness proof. |
| AC-01 | Matrix multiplication exponent two | No exponent improvement established. |
| AC-02 | Rank of 3-by-3 matrix multiplication | No new exact decomposition or lower-bound certificate. |
| AC-03 | Border rank of 3-by-3 matrix multiplication | No new degeneration or lower-bound certificate. |
| AC-04 | Asymptotic rank of a small Coppersmith–Winograd tensor | No new asymptotic-rank bound. |
| AC-05 | Asymptotic rank of tight tensors | No proof of the universal statement. |
| AC-06 | An explicit family with quadratic border rank | No family meeting the full construction and complexity requirements. |
| AC-07 | Scholz–Brauer addition-chain inequality | No all-parameter construction. |
| AC-08 | Knuth–Stolarsky small-step inequality | No all-parameter inequality or counterexample. |
| AC-09 | Deterministic commutative Edmonds problem | No algorithm meeting the full complexity target. |
| AC-10 | Explicit rational rigid matrices | No family meeting the full rigidity target. |
| AC-11 | Least positive sign-matrix permanent | Exact attaining matrices for the finite orders in `claims.json`. |
| AC-12 | Restricted-family realization of every permanent | Exact finite-order range certificates for the orders in `claims.json`. |
| AC-13 | Near-quadratic deterministic multiplication verification | No algorithm meeting the full bit-complexity target. |

## Interpretation

The universal divisibility lemma used for AC-11 is established background, not a claimed new theorem. The new deliverable is an explicit, independently checkable set of attaining matrices. Wanless's cited 2005 paper gives constructions through order 20. That fact alone does not establish that the additional orders in this package are first in the literature; priority has not been established.

For AC-12, a sample of matrices cannot show that no other values occur. Sampling was used only to locate some restricted witnesses. The submitted completeness claim relies on exhaustive representative coverage and, where used, a proved branch bound. Every numerical value admitted to the candidate range has an explicit restricted-family witness checked separately with exact arithmetic.

No purported all-orders induction, tensor decomposition, rigidity construction, or addition-chain proof is included without a completed verification. No external submission has been made.
