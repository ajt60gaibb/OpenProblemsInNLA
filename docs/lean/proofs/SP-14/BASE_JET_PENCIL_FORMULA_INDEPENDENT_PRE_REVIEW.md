# SP-14 base-jet pencil formula: independent mathematical pre-review

**Reviewer:** `/root/tr14_frob_review` (independent AI agent), 10 October 2026. **Verdict:** APPROVE the frozen formula contract for Lean implementation. This approval is for the exact finite base-pencil polynomial, not for the SP-14 counterexample or `NLA.Statements.SP14.Target`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`BASE_JET_PENCIL_FORMULA_PRE_REVIEW.md`** | **`34382ee1010794845f95e1d3138d30e2b59202d10a1025f0630d4834c9a98957`** |
| Canonical `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Audited `lean-statements/NLA/Proofs/SP14/BaseJetFourierMatrix.lean` | `03ded74b3244a27cad27e829dd634b6a54a32f17b4a3e468640f1372da8285bd` |

I compared the contract with Proposition “Odd-symbol pencil and its jets,” the compiled `baseG_square` and selected-block cofactor theorem, and the independently reviewed actual-Fourier `oddB`/`oddC` bridge. The source-locked Jacobian has index `q_source=m-d-1`, so its coefficient `-2(k+1) binom(1/2,d-k)` for `k≤d` matches the proposed formula with `baseCoeff(d-k)`.

## Algebra and endpoint checks

- Under `2q≤m+1`, every `d<q` satisfies `d≤m` and each correction shift `s_d=m-d` is positive. Its minimum is `m-q+1`, and `2(m-q+1)≥m+1`; thus two corrections have total shift beyond the highest matrix superdiagonal `m`. Consequently `E²=0`, including the equality-bound case `2q=m+1`. For `q=0`, the empty sum gives `E=0`; for `m=0`, the bound forces `q=0`.
- `baseG` is the upper Toeplitz matrix `Σ_{r=0}^m baseCoeff(r) U^r`. The proposed `E` is `Σ_{d<q}v_d U^(m-d)`. These identities imply `G₀E=EG₀` and `G_v=G₀+E`; the latter is exactly the selected-Fourier matrix already proved for the full restored symbol. Together with the kernel-checked `G₀²=I+U` and `E²=0`, they give `G_v²-(1+t)U=I-tU+2G₀E` for all `t∈ℂ`.
- Nilpotence `U^(m+1)=0` makes `W=Σ_{k=0}^m t^kU^k` a two-sided inverse of `F=I-tU`. Every factor is a polynomial in `U`, so `(WG₀E)²=0`; multiplication verifies `(F+2G₀E)^(-1)=W-2WG₀EW`. The pencil is upper triangular with diagonal one, hence determinant one even at `m=0`. The generic reviewed cofactor identity therefore identifies its upper-right inverse entry with the characteristic-polynomial quotient evaluated at `1+t`.
- The `U^m` coefficient of `W` is `t^m`. In `WG₀EW`, the `d`th correction contributes to `U^m` precisely when `k_left+r+k_right=d`. For `k=k_left+k_right`, the range is `0≤k≤d`, and there are exactly `k+1` ordered pairs. Its corner coefficient is therefore `Σ_{k=0}^d (k+1)baseCoeff(d-k)t^k`; the inverse contributes the advertised factor `-2v_d`. This proves the polynomial formula pointwise in `t` and hence as a polynomial, with the **actual** frozen `oddJetPolynomial` via the reviewed Fourier blocks.
- At `m=0,q=0`, the polynomial is `1` and the actual `T₁` characteristic polynomial is `X`. At any `q=0`, it is `X^m`. At `m=1,q=1`, it is `X-2v₀`; at `m=3,q=2`, it is `X³-2v₀-v₁-4v₁X`. I independently checked all 40 allowed `(m,q,w)` cases with `m≤3`, `w∈{-2,-1,0,1,2}`, and rational `v_d=(d+1)/3` by exact-fraction determinants of the finite odd block matrix. These checks supplement the all-order algebra and do not serve as its proof.

The eventual Lean theorem must retain `2q≤m+1`, all `m,q,v`, the exact `baseJetSymbol`, and `oddJetPolynomial`; a corner-only model would be insufficient. No background-pencil invertibility or genericity premise is needed for this base identity. A frozen implementation still needs separate exact-signature, proof-escape, imported LeanCert kernel, and transitive-axiom review. The correction-vector solve, Jacobian rank, all-background stages, infinite symbol, and final negative target remain open.

Changed contract or source bytes reopen this review.
