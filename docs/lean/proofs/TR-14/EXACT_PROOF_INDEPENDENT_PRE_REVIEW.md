# TR-14 exact full-proof route: independent mathematical pre-review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 10 October 2026. **Verdict:** APPROVE frozen `EXACT_PROOF_PRE_REVIEW.md` as a faithful pre-implementation contract for the **unchanged full target**. This approval is mathematical/source-level only; it does not prove `NLA.Statements.TR14.Target` in Lean.

The proposed exported theorem `target : NLA.Statements.TR14.Target` keeps all canonical quantifiers: `m≥3`, `n≥2`, every complex Hankel moment vector `h`, and **every** natural width `r`. The frozen `HankelIndex` sums zero-based coordinate values, equal to the canonical one-based sum minus `m`. `OrdinaryWidth` permits independent factors in each mode, while `SymmetricWidth` uses one vector and a complex scalar per summand. The reverse width implication absorbs that scalar into one mode, including the empty `r=0` case. For the forward implication, the source's nonzero exact-rank equality must be converted to every width by zero padding; zero tensors have rank zero and must be handled separately. No genericity, Vandermonde, or border-rank restriction can enter the final theorem.

The canonical `solution.tex`, Theorem 1.1 and §§2–5, states the nonzero formula `min(D−r₀+2, (m−1)r₀−(m−2)s)` with `D=m(n−1)`, `r₀` the least apolar degree (proved equal to the middle catalecticant rank), and `s` the number of **distinct projective** roots of a minimal apolar polynomial. The proposed contract distinguishes `r₀` from the arbitrary target width. In the nonunique balanced case `D=2r₀−2`, the first branch is `r₀` and the second is at least `r₀` because `s≤r₀`; the formula is independent of the chosen apolar polynomial. This includes repeated-root and infinity-chart cases.

The local interpolation count in the source is exactly `N_a=(m−1)(ℓ_a−1)+1` nodes for a root of multiplicity `ℓ_a`, including `N_a=1` when `ℓ_a=1`. Summing gives `(m−1)r₀−(m−2)s`. The second upper construction uses a squarefree apolar polynomial of degree `D−r₀+2`. Both are symmetric decompositions under the frozen coordinate semantics after chart changes; zero weights can be padded or removed.

The contract correctly identifies the decisive lower-bound obligation as an **arbitrary minimum ordinary decomposition** with mode-dependent factors. In the source, graph subspaces in `A×ℂ^R` and a Frobenius functional satisfy the contextual product-space lemma only after proving products of all but one mode surject onto `A`. Reduced stabilizers partition whole local factors. For each block, the source obtains `R_j ≥ m·min(n,r_j)−r_j−m+2`. If some `r_j≥n`, this yields `R≥D−r₀+2`; if every `r_j<n`, summing with `t≤s` yields `R≥(m−1)r₀−(m−2)s`. A lower bound for symmetric, Vandermonde, generic, or reduced-algebra decompositions alone would not prove the frozen target. These finite-algebra and product-space claims must be proved in Lean; no external theorem may be inserted as a new axiom.

| Reviewed input | SHA-256 |
| --- | --- |
| **`docs/lean/proofs/TR-14/EXACT_PROOF_PRE_REVIEW.md`** | **`abd73514c57e2d8c5f6a2709273a43ad282c854c8647e99855492f23052a6698`** |
| Canonical `tensor-computations/TR-14/README.md` | `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86` |
| Cited `tensor-computations/TR-14/solution.tex` | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6` |
| Frozen `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |

Changed source bytes reopen this review. TR-14 remains statement-only until the exact target theorem is implemented and independently kernel checked.
