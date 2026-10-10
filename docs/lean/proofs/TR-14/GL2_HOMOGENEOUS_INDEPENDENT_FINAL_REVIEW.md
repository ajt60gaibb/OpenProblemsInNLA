# TR-14 homogeneous chart foundation: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen `GL2Homogeneous.lean` for aggregate import as a partial TR-14 lemma. This is not a proof of `NLA.Statements.TR14.Target`.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/TR14/GL2Homogeneous.lean` | `5d91423c625d687c034b3df7cd14b1a652a707edc4ee436e36d44521baa0f4b7` |
| Independent chart mathematical pre-review | `0b225faaed0d307e582bc75946b540e872d1fdad927495e27d18f847d0b0ceb2` |
| Canonical `tensor-computations/TR-14/solution.tex` | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66c282716c14bc6` |
| Frozen `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Separately imported audit source, `/private/tmp/tr14-gl2homogeneous-independent-audit.lean` | `72b2211fc02339d253a82978306726d08c339a6dbc48942577d01e8499fbb5af` |

The source uses the genuine degree-`d` homogeneous submodule of `MvPolynomial (Fin 2) ℂ`, with canonical monomials `X^(d-i)Y^i` and no moment binomial factors. `chartSubst z` sends `(X,Y)` to `(Y,X+zY)`, and `chartSubstInv z` sends it to `(Y-zX,X)`. Composing these substitutions on each generator gives the identity in both directions. The homogeneous-degree lemmas show that both restrict to each degree, including degree zero, so `chartPhiEquiv z d` is an actual complex-linear equivalence. `binaryMul` has the summed degree, and `chartPhi_mul` is the exact multiplicativity identity.

`BinaryMoment D` is the full complex-linear dual of the homogeneous degree-`D` forms. `chartMoment z L = L ∘ (chartPhiEquiv z D)⁻¹`; the theorem `chartMoment_mul_pairing` has arbitrary degrees `d,e`, a functional of degree `d+e`, and all forms of those degrees. Its proof applies multiplicativity and the inverse equivalence. This is precisely the inverse-dual orientation of the reviewed chart contract; neither complex conjugation nor coefficient rescaling occurs.

The independent imported audit completed with exit code zero under pinned Lean 4.33.1 and LeanCert `kernel` mode. It checked every public type above, reran `#assert_trust kernel` on the equivalence, multiplication, and inverse-dual theorem, and printed their transitive axiom sets. Each set is exactly `[propext, Classical.choice, Quot.sound]`. A source scan found no `sorry`, `admit`, introduced `axiom`, `native_decide`, `unsafe`, or `run_tac` escape.

This module does not yet construct a functional from each frozen moment vector, connect the dual pairing to the exact apolar convolution, normalize a minimal form, transport every Hankel mode or width, or prove the all-width target. Those obligations remain separate. A change to the frozen source bytes requires a new final review.
