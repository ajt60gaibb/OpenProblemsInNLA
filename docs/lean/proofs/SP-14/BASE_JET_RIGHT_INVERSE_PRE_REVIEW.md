# SP-14 constructive base-pencil jet right inverse: pre-proof contract

**Author:** `/root/sp14_base_proof`, 10 October 2026. **Status:** frozen for independent mathematical review; no Lean implementation authorized before approval. The original negative Target is `lean-statements/NLA/Statements/SP14.lean`, SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`. The mathematical source is `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex`, SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`, Proposition “Odd-symbol pencil and its jets,” especially its base Jacobian formula. This contract uses the frozen `FourierCoefficient`, actual `Toeplitz`, `baseExteriorSymbol`, `restoredNegativePacket`, `oddJetPolynomial`, and `baseCoeff` definitions. It does not replace the symbol or characteristic polynomial with a surrogate.

## Exact constructive finite claim

For natural numbers `m,q` with `2*q ≤ m+1`, and `v : Fin q → ℂ`, put

```lean
noncomputable def baseJetSymbol (m q : ℕ) (v : Fin q → ℂ) : Circle → ℂ :=
  fun z => baseExteriorSymbol z + restoredNegativePacket m q v z
```

Thus the current section contains the **restored** source packet. The independently reviewed own-order invisibility of its `K_m` part, at order `2*m+1`, is needed to replace it in the calculation by the raw `L_v`; the full `D_v` is not asserted invisible. Define the explicit polynomial

\[
P_{m,q,v}(t)=t^m-2\sum_{d=0}^{q-1}v_d
                  \sum_{k=0}^{d}(k+1)c_{d-k}t^k,
\qquad c_r=\binom{1/2}{r}=\texttt{baseCoeff}\;r.
\]

The primary theorem must state equality of the **actual** frozen odd jet polynomial:

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

The exact algebra underneath is `G=G₀+E`, where `G₀=baseG m`, `E=Σ_{d<q}v_d U^(m-d)`, and `G₀²=I+U`. The size condition gives `E²=0`. All three upper Toeplitz matrices commute, so `H=G²-U=I+2G₀E`. The inverse of `H-tU` is

\[
(I-tU)^{-1}-2(I-tU)^{-1}G_0E(I-tU)^{-1};
\]

the second correction squares to zero. Its upper-right entry is the displayed polynomial because a total shift of `m` can be obtained by `k` powers of `tU` in exactly `k+1` left/right placements, leaving coefficient `c_{d-k}`. The source's odd-pencil determinant identity, or an equivalent direct finite determinant calculation, must identify this corner polynomial with the frozen `oddJetPolynomial`; `det(H-tU)=1` because it is unit upper triangular. No use of an analytic inverse at the boundary is needed for this finite algebra.

For `0 ≤ h ≤ q`, the first `h` coefficients are linear in the real vector. Define the **real** source matrix

\[
J^0_{kd}=\begin{cases}
-2(k+1)\binom{1/2}{d-k},&k\le d,\\
0,&k>d,
\end{cases}\qquad 0\le k,d<h.
\]

The Lean module should define `baseJetMatrix (h : ℕ) : Matrix (Fin h) (Fin h) ℝ` by that formula using `Ring.choose (1/2 : ℝ)`, and prove its complex cast agrees with `baseCoeff`. It should define the explicit real solve `baseJetSolve h y := (baseJetMatrix h)⁻¹ *ᵥ y`, or the equivalent descending recursion, for every `y : Fin h → ℝ`. Pad this `Fin h` vector by zero to `Fin q`, cast to `ℂ`, and prove these public outcomes:

1. `baseJetMatrix h` is invertible for every `h`, with upper-triangular diagonal `-2*(k+1)` and determinant `∏ k : Fin h, -2*(k.val+1) ≠ 0`.
2. For every `m,q,h` with `2*q ≤ m+1` and `h ≤ q`, and every real target jet `y`, the padded actual symbol satisfies `∀ k : Fin h, (oddJetPolynomial (baseJetSymbol m q (pad (baseJetSolve h y))) m).coeff k = (y k : ℂ)`. In particular `y=0` yields an explicit real vector with `JetVanishing` at the actual section, and the base point `v=0` already satisfies this when `h≤m`.
3. The finite real jet map has the exact difference law `F(u')-F(u)=J⁰*(u'-u)` on the first `h` coordinates (after zero-padding). Thus its Jacobian is `J⁰` **at every vector** and has full row rank `h`. This is regularity of the actual finite characteristic-polynomial equations in the source's real variables, not merely a formal invertibility assertion for an unrelated matrix.

The explicit solve may be proved by ordinary triangular back-substitution. Its `k`th equation is

\[
y_k=-2(k+1)\sum_{d=k}^{h-1}c_{d-k}u_d,
\]

whose coefficient of `u_k` is `-2(k+1)c_0=-2(k+1)≠0`. Since the coefficients `c_r` are real, real input produces real output. The matrix inverse is fixed by `h`; no existential choice of a nonlinear root is involved.

## Endpoint and exact arithmetic checks

At `m=0`, the size inequality forces `q=h=0`; `P=1`, the Toeplitz characteristic polynomial is `X`, and the empty matrix is invertible. At `q=0` for any `m`, `P=t^m`; `h=0` makes the solve and rank statements empty but valid. At `m=1,q=h=1`, `P=t-2v₀` and `J⁰=[-2]`. At `m=3,q=h=2`,

\[
P=t^3-2v_0-v_1-4v_1t,\qquad
J^0=\begin{pmatrix}-2&-1\\0&-4\end{pmatrix}.
\]

Independent exact rational determinant evaluations of the actual `T_{2m+1}` at `w=-2,-1,0,1,2`, with nonzero rational correction vectors, agree with `w P(w²-1)` for `(m,q)=(0,0),(1,1),(2,1),(3,2)`. These are checks only; the Lean proof must cover all allowed `m,q`.

## Separate full stage gate and feasibility audit

The base theorem is a **constructive model**, not the source's perturbed stage. The next required all-background theorem must fix a prior finite source background consisting of the exterior base, earlier finite positive packets, and earlier finite restored negative packets, then add the current positive packet `τ_j s^{m_{j-1}}(1+s)`. It must use exactly the source's `θ=2^-10000`, `σ=3/8`, `q=3m/8`, `h=⌊θm⌋`, `m` divisible by eight and `m≥8m_{j-1}`. Under a concrete source admissibility predicate (chronological support separation and the four explicit weighted-neighborhood/norm budgets, **without** assuming a jet root, surjective Jacobian, or a right inverse), the conclusion for every sufficiently large such `m` is an actual real `v : Fin q → ℝ` for which the restored symbol has `JetVanishing ... m h`, the real Jacobian of these same first-`h` equations has row rank `h`, the preconditioned `R₁,R_{1/2}` bounds are strict, and all four restored increment budgets are strict. The source's current-order `K_m` invisibility permits computing these jets with `L_v`, while `D_v` itself remains visible at its selected section. This is the finite stage gate needed before a deterministic infinite selection can be formalized.

Proving that theorem is substantially more expensive than the base module. The exact source route needs the finite pencil/resolvent identity, background-dependent conformal coordinate, two compatible Sobolev isomorphisms with explicit numerical constants, the forcing estimate for `h≈θm`, oversampling to a bounded finite right inverse, separated-corner nonlinear feedback and contraction, then realness, rank, and weighted restoration estimates. These analytic dependencies are not yet formalized in this workspace. The base `J⁰` theorem supplies the exact source preconditioner and proves that the model system is regular, but it **cannot** by itself justify persistence for all admissible backgrounds or the open norm budgets. The all-background theorem should be independently contracted and reviewed before implementation; no final `Target` follows from the present base claim.
