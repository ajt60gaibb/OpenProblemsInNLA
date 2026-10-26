# PF-05: independent full-target fidelity and assembly review

Reviewer: statement/zero-branch agent (`fr05_statement`). Date: 2026-10-18.

Mathematical and source verdict: **APPROVE the literal complete Target and the final assembly.** The isolated final kernel receipt is **PASS: 43 source builds** across the two immutable stages, followed by the successful literal live/frozen Target consumer and seven final exported-constant kernel/std3 checks (plus the earlier fifteen checks). This is a local proof review, not a Linux CI/Comparator success claim.

## Frozen boundary and assembly bytes

| Input | SHA-256 |
| --- | --- |
| Live `lean-statements/NLA/Statements/PF05.lean` | `3ac9a2fb395d96c3b61c6f2593144caac010da4bfafd2d96f86627aa7a75859d` |
| Frozen `lean-statements/Reviewed/PF05.lean` | `df79daee68563e5bb6a6d85cf70246bf2154f12bcc5fe5a6a806e8009e558b7f` |
| `lean-statements/NLA/Proofs/PF05/PositiveUniqueness.lean` | `27fc7c61ace8a86cdcfcd348cd2a457de2084a2e4409aaec5e98dbc028add878` |
| `lean-statements/NLA/Proofs/PF05/Final.lean` | `9fec01759722b38b8fab73a3115f9b6546df3cba1bdb7b51f53e0b8c3b3db0d9` |
| Canonical `nonnegative-and-positive-factorizations/PF-05/README.md` at review | `f7acc0629067696f7aa2828673740e286730fb9654348b742752eb146a840f71` |

The approved boundary is unchanged from both fresh preproof reviews. The target quantifies over every finite pair of dimensions, every real entrywise nonnegative ordinary-rank-three matrix of PSD rank two, and every actual size-two PSD factorization. The forward and reverse statements are the literal equivalence of actual straight-segment infinitesimal rigidity and uniqueness up to one actual invertible real congruence with its actual inverse dual. Positive entries, nonzero factors, distinct rays, favorable charts, and local topology are not added to the final theorem.

The canonical PF-05 identifier remains registered at `nonnegative-and-positive-factorizations/PF-05/README.md`. No problem number, canonical path, original source or mathematical target is changed by these proof modules. The rank-two PSD-rank premise is retained in the exact theorem even though rank three and the given size-two factorization already imply it. Its redundancy is not a reason to alter the original statement.

## Independent authorship coverage

I independently read the final `PositiveUniqueness` and `Final` sources, the solver's zero restriction/core and unrestricted reverse route, and the root's conic classification. The four chart/conic gates have the separate hash-bound source review `CONIC_COMMON_CHART_INDEPENDENT_REVIEW_2_2026-10-18.md` and private 23-source rebuild.

I authored the seven new zero-normal-form/zero-pair forward modules and the six new quartic/contact/strict-PSD modules. Their implementations are **not counted as independently reviewed by this report**. The solver's `SIGNED_QUARTIC_AND_CONIC_INDEPENDENT_REVIEW_1_2026-10-18.md` (SHA-256 `eb067f21b14315774dcf50677bb8d84842b0cdcf2b525869d975c312f503624b`) independently covers the frozen signed-quartic chain; the separate verifier's zero-pair review provides the zero-branch coverage. The current full closure rebuild checks these modules mechanically without changing that authorship distinction. The seven retained support sources remain unchanged and are also covered by the fresh preproof source review.

## Complete mathematical assembly

For the strictly positive branch, rank three rules out empty dimensions and supplies a positive entry witnessing that every factor is nonzero. One actual invertible common shear puts every primal 00 and dual 11 entry in a positive chart. Congruence transports the actual straight-rigidity property. Only then does retained positive-ray compression pick actual representative factors, so the chart inequalities survive simply by selecting indices. The compressed instance preserves positive entries, rank three and both exact properties. The signed-quartic proof forces every actual alternative's determinant quartic to vanish. The homogeneous bridge retains the missing point at infinity, and the proved conic classification supplies actual congruence. The proof then uses the retained equivalence in the correct direction to restore all repeated rays and composes the actual original-coordinate congruence.

For arbitrary zero patterns, `rigid_implies_unique` splits on an actual nonzero primal/dual pair with zero matrix entry. The displayed zero-pair theorem covers that branch directly in the original coordinates. In the complementary branch, the actual selection deletes exactly zero factors, with no assumed core. Nonzero factors have strictly positive remaining entries. The actual coordinate spans prove rank remains three. Restriction and zero extension preserve both full frozen properties; the proof invokes the proved positive branch and restores every original zero position. Thus a zero row or column is never silently removed from the final uniqueness conclusion.

The unrestricted reverse direction first extracts the actual unique coordinate operator of the frozen first-order trace equations. It retains the primal straight path and uses the actual inverse pencil on the weighted dual side. Definite and strict-normal singular factors stay PSD by actual one-sided calculus; the flat rank-one case uses its proved proportional direction and exact inverse eigenvector identity. Zero factors stay zero. A finite common interval produces exact alternative PSD factorizations. Uniqueness identifies the entire actual operator line with congruence operators by actual full row span. Four fixed rank-one tests force the affine congruence line to be scalar. This recovers precisely the one common scalar and opposite dual scalar required by the frozen definition, without selecting or differentiating congruence representatives.

`Final.target` consumes all literal Target binders and applies these unrestricted implications. It has no premise asserting another part of the target. No external theorem equivalent to PF-05, curve-selection oracle, quotient-connectedness oracle, or closed-orbit assumption remains in its import path as a hypothesis.

## Reproducible local evidence and limitations

The private audit extends the immutable 23-source conic/chart build to the entire actual final import closure and the frozen reviewed boundary. Previously built dependencies are reused only from that same private source snapshot, never from shared NLA proof objects. Each additional source is copied and hashed before building; every live byte is checked again afterward. The consumer checks literal live and frozen Target typing and their `rfl` identity, then LeanCert kernel trust and printed axioms for the final theorem and the assembly gates. The full input lock, individual logs, audit scripts, and result file are retained in `full-target-review-2-evidence/`. The first consumer used the obsolete namespace `NLA.Reviewed.PF05`; the retained harness-error log records that mistake. Correcting only the consumer to the actual frozen namespace `NLA.ReviewedStatements.PF05` made both literal target checks and their `rfl` identity pass. No proof or statement source changed. Source snapshots use `.lean.txt` suffixes.

Linux CI and the canonical Comparator are still separate required evidence. This review does not mark the public problem solved, alter its status or assert those checks have run. Package boundary and final wrapper reviews remain independent packaging obligations.
