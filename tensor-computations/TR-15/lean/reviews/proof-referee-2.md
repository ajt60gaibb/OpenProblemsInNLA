# TR-15 independent final proof referee 2

**APPROVE the complete seven-export mathematical formalization.** Referee: OpenAI Codex agent `/root`, independent of implementation agent `/root/leancert_examples`. Review date: 12 September 2026. This is a source-level and fresh local Lean proof review applying the relevant pinned Tau Ceti standards. It is not human peer review, a source-author endorsement, or a Linux Comparator result.

## Frozen boundary and source correspondence

Both independent statement approvals preceded implementation. The reviewed proof freeze is SHA256 `1263937a8aeef77192d2eaf434457c36abefc77a7aefbd25fdf0dbd854ed7f6c`. My executable [audit](proof-referee-2-root-evidence/audit.py) confirms all 75 frozen project files and all six original source files remain unchanged and compares each original source to its actual upstream Git blob. The exact seven public signatures match the approved Challenge; Comparator selects those seven with no definition exceptions and only the standard foundational axioms.

I read the actual Definitions, complete Proof and all Solution exports, rechecked the canonical statement and my independent statement-stage tensor reconstruction, and inspected the relevant actual Mathlib IVT and LeanCert checker theorems. The formal target contains all odd m≥3, q≥2, n≥2 and real common generators of length qm(n−1)+1. Its lower order/dimension and higher order/dimension are exact. Each tensor is the full array on ordered tuples; actual index bounds and the same generating vector are preserved. H-eigenpairs include a real nonzero vector and signed coordinate powers. No assumed tensor coefficients, sampled spectrum, associated-Hankel PSD condition, strong-Hankel hypothesis or eigenpair-existence premise enters the conjecture.

## Mathematical and trust audit

The lower contraction is derived from the actual ordered sum using a proved pair equivalence. Its first component is the sum of all three coordinate squares and (x₀+x₂)², strictly positive for every nonzero vector. The genuine eigenpair equation then excludes every nonpositive real eigenvalue, without enumerating roots. My earlier exact reconstruction of all 27 entries agrees with the coefficients used by the proof.

For the higher tensor at (0,1), the proof shows every contracted tuple except the all-one tuple has a zero vector factor. Exactly one summand survives per component, giving (0,−1) and the genuine negative H-eigenpair. This reduces the ordered sum without changing the tensor or weights. My independent finite reconstruction of all 64 relevant entries agrees.

Nonvacuity is separately proved using the actual polynomial 2t⁴+2t³+3t²−4t−1. Continuity and endpoint values −1 and 2 feed Mathlib's actual open-interval IVT. Its root t∈(0,1) yields the nonzero vector (1,0,t), eigenvalue 2+2t+2t² and every contraction equation. Neither a numerical root nor an existence assumption is used. The final contradiction uses the full original implication at the admissible m=3,q=2,n=2 instance.

I freshly re-elaborated Definitions, Proof and Solution into a separate target artifact prefix; all three exited zero with no warnings, and all 15 internal/public kernel trust and transitive-axiom reports contain exactly `propext`, `Classical.choice` and `Quot.sound`. All ten dependency Git trees are clean and equal their manifest pins. These macOS checks reuse pinned dependency caches; they are not a full dependency-source rebuild or the pending Linux run.

My fresh [actual-environment inspection](proof-referee-2-root-evidence/Inspect.lean) traverses 46 project declarations, including private/generated helpers, and checks 14 material dependencies. It retains actual ordered-sum/product-zero lemmas, open-interval IVT, all substantive implementation exports and `LeanCert.Validity.verify_strict_upper_bound_dyadic_checked`. It prints the actual strict −1<0 proof and repeats the seven public kernel/axiom audits.

A separate [certificate-helper inspection](proof-referee-2-root-evidence/InspectCertificate.lean) verifies the actual `checkStrictUpperBoundDyadicChecked ... = true` fact, not merely the precision side condition. Its term is `of_decide_eq_true (id (Eq.refl true))`, checked by kernel reduction at [0,0], precision −53, depth 10. The certificate is consumed by the upper negative pair, the counterexample and the full negation. There is no native-execution axiom or decorative unused interval call.

## Packaging observation and remaining gate

The frozen project README still contains the statement-stage claim that there is no proof implementation. This is a documentation defect, not a mathematical defect: preserve its historical bytes and update the current README during packaging to report the completed proof/reviews and the still-pending Linux checks. Do not alter the frozen mathematical statements or proof to fix this text.

The project requires truthful v0.4 metadata and an actual successful Linux Comparator/default-kernel/control run with independently audited original artifacts before a `Lean verified` promotion or completed upstream publication. The current mathematical status remains Solved. All source attribution remains Matthew J. Colbrook; formalization credit is George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI assistance and no published email.

The [evidence manifest](proof-referee-2-root-evidence/manifest.json) is SHA256 `43c15c958c6f1441dfaecceb3e45ec713e2c9316227dfbd9ad5591f49b3b742e`. It binds fresh commands/logs, source identity, standard-three reports, both actual inspections, dependency pins and the exact audit. No frozen implementation byte changed for this review.
