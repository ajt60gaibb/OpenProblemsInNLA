# TR-14 apolar map and minimal degree: independent pre-proof review

**Reviewer:** `/root` (AI agent), 10 October 2026. **Verdict:** APPROVE frozen `APOLAR_MINIMAL_PRE_REVIEW.md` as the exact finite apolar/minimal-degree contract for implementation. This approves a mathematical subproblem, not a Lean proof or the full `TR14.Target`.

I checked the contract against the canonical `solution.tex` definition of `I_d`, its moment-algebra lemma, and the frozen zero-based `Hankel` target. For each `0≤d≤D`, the proposed map has coefficients `Σ_{i=0}^d g_i h_{i+j}` for **every** `0≤j≤D−d`, with no conjugation or omitted endpoint. Its domain has `d+1` coefficients and its codomain has `D−d+1` equations. It retains coefficient vectors with `g_d=0`, including homogeneous roots at infinity, and explicitly postpones the source convention for `d>D`. The suggested `X` and `Y` extensions of an apolar vector preserve all required equations with the stated reduced range.

For `h≠0`, `I₀=0` follows from a nonzero moment; for `h=0`, every apolar map is zero and the zero tensor stays separate. At `d*=⌊D/2⌋+1` with `D≥1`, the domain has more dimensions than the codomain, so a nonzero kernel vector exists for **every** `h`. The even and odd dimension tables are correct, including `D=1`, `D=2`, and the balanced even endpoint. Selecting the least witness gives `1≤r₀≤d*`, a nonzero vector in `I_{r₀}`, and no nonzero vector in any lower `I_d`. The arithmetic split `D=2r₀−2` or `D≥2r₀−1` follows from the bound and retains the balanced case. No monic-chart, squarefree, genericity, or selected-width premise enters these claims.

The proposed Lean declarations are API sketches, with proof terms to establish index bounds. Their final elaborated signatures and source need a new independent imported LeanCert kernel and axiom audit. The quotient pairing, catalecticant rank, symmetric constructions, and arbitrary ordinary-rank lower bound are still open, so this pre-review does not upgrade TR-14 to a full proof.

| Reviewed input | SHA-256 |
| --- | --- |
| **`APOLAR_MINIMAL_PRE_REVIEW.md`** | **`93908b1804fdd4f2504382e59a6a2b2d50b5544e5c139d37ace3f530b30a4b23`** |
| Canonical `README.md` | `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86` |
| Canonical `solution.tex` | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6` |
| Frozen `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Parent `MOMENT_ALGEBRA_PRE_REVIEW.md` | `2297de29286de55999709753278dcf84c1b4dd67640f4064baa98ba93165a840` |
| Frozen `MomentIndex.lean` | `93932adde8ff14713d19a1c813a0ec2ea09a319cff29af242b5028a51ac39435` |

Changed contract or source bytes reopen this review.
