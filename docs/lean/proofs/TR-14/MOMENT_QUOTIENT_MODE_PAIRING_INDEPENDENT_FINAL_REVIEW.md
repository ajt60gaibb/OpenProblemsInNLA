# TR-14 moment-to-quotient mode pairing: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen source for aggregate import. It proves the genuine affine polynomial quotient image and exact all-moment Hankel pairing, not a CRT or width theorem.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/TR14/MomentQuotientModePairing.lean` | `24adc0f2e21ee8f84deb8ef4d6eddc8cc056327c2601e69f7c4a2a2cb35ae6cf` |
| Exact moment-to-quotient contract | `d9c791805617767bc2cf2d933a9d83ed9b188c6f6de614ee7f697d5d93d4f114` |
| Independent mathematical pre-review | `b87a65c54a92457396cade54c183d7f0a0f79f1e869c9610e9883a2d130a69b9` |
| Canonical `solution.tex` | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6` |
| Frozen `NLA.Statements.TR14` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Separate imported audit `/private/tmp/tr14-momentquotientmode-independent-audit.lean` | `21dd27228f08fb5f84bbeaf6ac07ff09ddd8a0985d92a1e0ab827836200b2886` |

The source defines `p_v(t)=Σ_i v_i t^i` in the genuine polynomial ring and proves its image in `AdjoinRoot g` equals the separate coordinate sum `Σ_i v_iτ^i`. The finite product of these quotient sums expands over every mode-index function `Fin m→Fin(q+1)` exactly once. Quotient-root powers multiply to `τ^(Σ_k i_k)`, where the exponent is precisely the frozen zero-based `HankelIndex`. The supplied moment identity covers all exponents through `D=mq`, including the top term; applying the linear functional gives the frozen multilinear Hankel pairing with no factorial or binomial factors.

The result holds for all natural `m,q`, including `m=0` and `q=0`, and requires no false bound on the quotient degree relative to the mode size. Two corollaries obtain the all-moment premise from the previously audited monic recurrence and exact apolar equations. No Frobenius, CRT, or local factorization hypothesis enters these statements.

The pinned Lean 4.33.1 direct module build passed 3,036 jobs. My separate imported LeanCert audit exited zero, checked all public signatures, reran `#assert_trust kernel`, and printed only `[propext, Classical.choice, Quot.sound]` for both the abstract all-moment and apolar corollary. A frozen-source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape. Changed source bytes require a new review.

CRT, local Frobenius roots, the symmetric upper constructions, arbitrary ordinary lower bound, and full TR-14 Target remain open.
