# SP-14 base-jet pencil formula: pre-proof contract

**Author:** `/root/sp14_base_proof`, 10 October 2026. **Status:** frozen for independent mathematical review before any Lean source is written for this formula. The fixed original `Target` is `lean-statements/NLA/Statements/SP14.lean`, SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`; the source is `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex`, SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`, Proposition “Odd-symbol pencil and its jets.” This is the finite algebra obligation inside the independently approved `BASE_JET_RIGHT_INVERSE_PRE_REVIEW.md` (SHA `bbcb1bfe...`). It depends on the independently reviewed generic cofactor identity and on final approval of the frozen actual-Fourier matrix bridge `BaseJetFourierMatrix.lean` (candidate SHA `03ded74b...`); the latter is not silently assumed complete until its final audit.

## Matrices and exact all-order statements

For `m,q:ℕ`, `v:Fin q→ℂ`, let `L=m+1`, `U=baseUpperShift m` (`L×L`, with `Uᵢⱼ=1` iff `j=i+1`), `G₀=baseG m`, and use the approved Fourier matrix `G_v=baseJetG m q v`. Define the source correction matrix

```lean
noncomputable def baseJetE (m q : ℕ) (v : Fin q → ℂ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  fun i j => ∑ d : Fin q,
    if j.val = i.val + (m - d.val) then v d else 0
```

Under `2*q≤m+1`, prove the exact **matrix** identities `G_v=G₀+E`, `E*E=0`, `G₀*E=E*G₀`, and

\[
G_v^2-(1+t)U=I-tU+2G_0E
\]

for every `t:ℂ`. This condition gives `m-d≥m-q+1>m/2`, so no two `E` shifts can fit in an `L×L` matrix; it also makes every added entry strictly superdiagonal. The `G₀` commutation is finite upper-Toeplitz convolution, or follows after proving `G₀=Σ_{r=0}^m c_rU^r` and `E=Σ_{d<q}v_dU^{m-d}`. The already kernel-checked `baseG_square` gives `G₀²=I+U`.

Put `F(t)=I-tU` and `W(t)=Σ_{k=0}^m t^kU^k`. Since `U^(m+1)=0`, prove `F W=W F=I`. All factors are polynomials in `U` and commute. Therefore `(W G₀ E)^2=0` and

\[
[G_v^2-(1+t)U]^{-1}=W-2WG_0EW.
\]

The pencil is unit upper triangular, so its determinant is `1` for every `t`, including `m=0`. Combine its adjugate/inverse equality with the independently reviewed generic cofactor theorem and the actual `oddB/oddC` identities. The resulting **public theorem must mention the actual frozen `oddJetPolynomial`**, not only a model corner:

```lean
theorem baseJetPolynomial_formula (m q : ℕ) (hq : 2 * q ≤ m + 1)
    (v : Fin q → ℂ) :
    oddJetPolynomial (baseJetSymbol m q v) m =
      Polynomial.X ^ m -
        2 * ∑ d : Fin q, Polynomial.C (v d) *
          (∑ k ∈ Finset.range (d.val + 1),
            Polynomial.C (((k + 1 : ℕ) : ℂ) * baseCoeff (d.val - k)) *
              Polynomial.X ^ k)
```

The upper-right entry `W₀ₘ=t^m`. In `WG₀EW`, the coefficient of shift `m` from the `d`th packet is obtained when `k_left+r+k_right=d`. For a fixed `k=k_left+k_right≤d`, there are exactly `k+1` ordered nonnegative pairs; the remaining base coefficient is `c_{d-k}`. This gives the displayed double sum and verifies the source's index reversal `q_source=m-d-1`, hence `J⁰_{k,d}=-2(k+1)c_{d-k}` for `k≤d`.

## Endpoint and semantic checks

If `m=0`, the bound forces `q=0`, the matrices are `1×1`, `U=E=0`, and the formula is `oddJetPolynomial=1`; this agrees with the actual `T₁` characteristic polynomial `X`. If `q=0` at any `m`, `E=0` and the formula reduces to `X^m`, agreeing with the independently reviewed exterior base characteristic polynomial. If `m=1,q=1`, the formula is `X−2v₀` in the jet coordinate and the actual odd characteristic polynomial is `w((w²−1)−2v₀)`. If `m=3,q=2`, it is `X³−2v₀−v₁−4v₁X`. Exact rational determinant checks at `w=-2,-1,0,1,2` for all allowed `(m,q)` through `(3,2)` agree with these formulas. No invertibility of a background pencil is assumed; the base pencil is invertible because it is unit upper triangular for every `t`.

After this identity, a separate reviewed assembly must use the already kernel-checked real `baseJetMatrix`/`baseJetSolve` and the coefficient equality to produce the explicit real `v` for any target first-`h` jet and prove actual finite-system Jacobian rank. That base solvability remains distinct from the perturbed-background all-stage solvability, source norm budgets, infinite symbol, and negative `Target`.
