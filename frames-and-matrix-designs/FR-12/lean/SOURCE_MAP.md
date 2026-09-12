# FR-12 source and statement correspondence

All repository mathematical sources are read at upstream revision
`8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`. They remain unchanged.

| Source | Formal obligation |
| --- | --- |
| `frames-and-matrix-designs/FR-12/README.md`, original Statement | `IsRealHadamard`, `HadamardMatrices`, `hadamardCount`, and `CountingConjecture` preserve real sign entries, the actual Gram identity, labels, arbitrary positive C, and every positive multiple of four. |
| `frames-and-matrix-designs/FR-12/solution.md`, Exact target | `counting_semantics` proves the exact subtype finite and connects it to Mathlib's actual Hadamard predicate. |
| Same source, Lemma 1 | `doublingMatrix` restricts the matching family to pair each top label with a bottom label using a permutation. `injective_doubling` proves the actual matrix and recovery properties. |
| Same source, Theorem 1, factorial estimate | `factorial_doubling` proves m! H(m)^2 ≤ H(2m), precisely the weaker factor used by the source's iteration. The all-matching factor (2m−1)!! is not a formal export. |
| Same source, Theorem 1, existence and iteration | `power_two_nonempty` and `power_two_lower_bound` prove actual nonemptiness and the identical quantitative bound, indexed by K = k+2. |
| Same source, final contradiction | `counterexample` quantifies every positive real C and finds a strict failure; `not_countingConjecture` negates the full original target. |
| `references/stepaniants-fr12-2026-09-12/REVIEW.md` | Retained earlier informal AI review and provenance, not evidence that this Lean implementation is already verified. |

The supplied and retained analytic proof is credited to George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. Ferber, Jain and Zhao retain conjecture
and upper-bound attribution. The formalization does not claim to settle
Hadamard existence at all admissible orders, recover a matching upper bound,
prove the source's stronger recurrence, or certify historical priority.

## Primary library and workflow references

- Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`:
  `Mathlib/LinearAlgebra/Matrix/HadamardMatrix.lean` supplies the actual standard
  predicate and the one-sided-to-two-sided Gram theorem. Its requirements must
  be discharged for positive real matrix dimensions.
- At the same pin, `Mathlib/Data/Nat/Factorial/Basic.lean` supplies exact
  factorial bounds. The formalization must apply these to the actual subtype
  cardinalities; importing the file does not prove the desired recurrence.
- LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`: kernel trust auditing;
  no artificial interval certificate is required for the proposed exact proof.
- Forsythe `8d1b0c0545a77b40245e84705aa7d273e6c81e62`: the campaign's inherited
  Challenge/Solution split and compatible audited checker/exporter, with the
  documented Lean 4.33.1 adaptation in shared infrastructure. Apache 2.0.
- Schiffer `2938e277969c329caf154e48a3d8823f3635c7f1`: organizational example
  studied; no copied mathematical proof code is asserted.
- Tau Ceti review standards `afb424eda89e8ac96d9eb69f6a88972055a4cd1b`:
  independent statement and final proof correspondence, trust and evidence
  reviews as applicable to this exact mathematical theorem.
- `formalization.yaml` specification
  `99c678e569c7c4c0772db297c5ddd5e4c9b6322e`, schema v0.4: a truthful manifest
  will be added when the completed candidate is ready for Linux verification.

No new literature-resolution claim is made by this statement package. The
canonical retained bibliography and its bounded historical checks remain
unaltered. Actual Linux checking, final proof review and publication are future
gates, not findings implied by these references.
