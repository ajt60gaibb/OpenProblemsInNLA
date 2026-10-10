# Next full-target proof triage among statement-only Solved problems

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 10 October 2026. This is a read-only prioritization of the 35 Solved entries listed as statement-only in `INVENTORY.md`. None of the three candidates below has a live theorem proving its frozen `Target`; `#assert_statement` and LeanCert checks of their declarations do not constitute proofs. Permanent IDs, canonical READMEs, and frozen statements remain unchanged.

**Progress after this triage:** TR-14 now has [independently reviewed width-basics lemmas](TR-14/WIDTH_BASICS_INDEPENDENT_FINAL_REVIEW.md) and is classified as partial in the current inventory. Its full frozen `Target` remains unproved; the statement-only count is now 34.

| Priority | Exact frozen target and canonical proof source | Main formalization obstacle | Status |
| --- | --- | --- | --- |
| **TR-14: best self-contained next campaign** | `NLA.Statements.TR14.Target`: for every `m≥3`, `n≥2`, Hankel data `h`, and width `r`, `OrdinaryWidth (Hankel h) r ↔ SymmetricWidth (Hankel h) r`. The canonical [README](../../../tensor-computations/TR-14/README.md) cites a complete [solution.tex](../../../tensor-computations/TR-14/solution.tex), Theorem 1.1 and §§2–5, covering zero and exceptional tensors. | Formalize finite moment/apolar algebra, symmetric upper bounds, and the lower bound for **arbitrary ordinary** decompositions under its Frobenius constraint. The 906-line proof is substantial, but its central route is algebraic and does not rest on one unformalized external analytic or probabilistic theorem. Width equivalence must be established at every `r`, not just equality of generic ranks. | Frozen statement only; no live Lean proof. |
| **SP-11: shortest deduction once its external theorem exists** | `NLA.Statements.SP11.Target`: for every finite graph `G` on `n>0` vertices, construct a real symmetric matrix with exactly the prescribed off-diagonal graph pattern and `δ(G)≤n−rank(A)`. The canonical [README](../../../eigenvalues-and-inverse-problems/SP-11/README.md) cites the complete [solution.tex](../../../eigenvalues-and-inverse-problems/SP-11/solution.tex) application note. | The 132-line note deduces this from Hall's all-graph **PSD/SAP delta theorem**. That theorem is the mathematical substance and has no formal source in this project; citing the informal theorem or making it an axiom would not complete the kernel proof. Formalizing it could also support SP-12 after additional chromatic and induced-subgraph arguments. | Frozen statement only; no live Lean proof. |
| **SP-13: focused analytic route with a deep external input** | `NLA.Statements.SP13.Target`: arbitrary Hermitian sequence `H`, arbitrary complex perturbations `E` with `NuclearNorm(E n)/n→0`, and every continuous compactly supported complex test retain the frozen spectral distribution, without spectral-norm bounds. The canonical [README](../../../eigenvalues-and-inverse-problems/SP-13/README.md) cites a complete [solution.tex](../../../eigenvalues-and-inverse-problems/SP-13/solution.tex), §§2–5. | Formalize the cited dimension-independent weak-type triangular-truncation estimate, Schur decomposition and singular-value counting, then the full measure/test-function limit. The 318-line local proof is complete mathematically but depends on that published non-elementary estimate, unavailable as a Lean theorem here. | Frozen statement only; no live Lean proof. |

**Recommendation:** Start a new independent full-proof project with TR-14 if substantial finite-algebra formalization is available. SP-11 is attractive only together with a verified formalization of Hall's all-graph theorem. SP-13 needs a comparable analytic library project. None is a quick completion, and no target should be weakened to bypass these obstacles.

| Source | SHA-256 |
| --- | --- |
| `tensor-computations/TR-14/README.md` | `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86` |
| `tensor-computations/TR-14/solution.tex` | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6` |
| `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| `eigenvalues-and-inverse-problems/SP-11/README.md` | `8e3edc4c7c6c8b388ab7bbf87bc197b76756210b19338d27398af356016aa865` |
| `eigenvalues-and-inverse-problems/SP-11/solution.tex` | `a639991609d402f107035c9e970519273237dd4fee838bd91ee23a0ba71ac0d8` |
| `lean-statements/NLA/Statements/SP11.lean` | `7de112a24cb0b78894d495b840a77a58572cce574d5d77eda15381410c65b131` |
| `eigenvalues-and-inverse-problems/SP-13/README.md` | `3db39d15a2d3879c0e72a983dd78197bcc8b99ac256a07fcaeee5b6f0962a57a` |
| `eigenvalues-and-inverse-problems/SP-13/solution.tex` | `6045c4175a7723ca112a7b937797255f641480fefa55d21ce8d1414881ea15cd` |
| `lean-statements/NLA/Statements/SP13.lean` | `59b9796c201eb0991479586d4372bbaf4500ad26fcfadd2bb5691c29653b089b` |

Changed source bytes reopen the corresponding comparison.
