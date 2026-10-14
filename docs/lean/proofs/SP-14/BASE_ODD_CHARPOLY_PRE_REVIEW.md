# SP-14 base symbol, odd Toeplitz characteristic polynomial: pre-proof review

**Author:** `/root/sp14_base_proof`, 9 October 2026. **Status:** proposed for independent mathematical and numerical review before Lean implementation. This is a bounded identity for the source's **base** symbol, which has an outer annular extension and is not the final counterexample.

## Exact target and branch

Let `c₀=1` and `cₖ=binom(1/2,k)` for every natural `k`; equivalently `cₖ₊₁=((1/2−k)/(k+1))cₖ`. These are real numbers cast to `ℂ`, with `c₁=1/2`, `c₂=−1/8`, `c₃=1/16`. Define `g₀(s)=Σₖ₌₀^∞ cₖ s^(−k)` for `|s|>1`, and use its continuous boundary values on `|s|=1`. The coefficients are absolutely summable, so this boundary series is unambiguous and uniform. It is the branch of `√(1+s⁻¹)` analytic on the exterior, tending to `1` at infinity. Its square equals `1+s⁻¹`. At `s=−1` its boundary value is `0`. Merely selecting a pointwise complex square root from `g₀(s)^2=1+s⁻¹` is insufficient: the exterior branch and normalization fix the sign.

The actual circle symbol is `a₀(z)=z g₀(z²)`, equivalently the uniformly convergent Fourier series `Σₖ≥0 cₖ z^(1−2k)`. For every natural `m`, **including `m=0`**, the requested Lean theorem is the literal equality of complex polynomials

```lean
(NLA.Statements.SP14.Toeplitz BaseSymbol (2*m+1)).charpoly
  = Polynomial.X * (Polynomial.X^2 - 1)^m
```

where `BaseSymbol : Circle → ℂ` must be constructed from the above convergent series and proved equal to the stated exterior branch on the circle. The theorem uses the frozen `SP14.Toeplitz` and its real interval Fourier integral; no surrogate matrix may replace it in the final theorem. The natural-number exponent has no large-construction parameters.

## Fourier and index check

With `a_k=(1/(2π))∫₀²π a₀(e^{it})e^(−ikt)dt`, uniform absolute convergence and Fourier orthogonality yield

```text
a_k = c_r  if k=1−2r for r∈ℕ;
a_k = 0    otherwise, for every k∈ℤ.
```

The normalization is exactly `1/(2π)`; it is not a normalized-circle measure with an implicit sign. The `e^(−ikt)` sign makes the `z¹` mode `a₁=c₀=1` and the `z⁻¹` mode `a₋₁=c₁=1/2`. With row-minus-column Toeplitz indexing, the order-three matrix is

```text
[0  1/2  0  ]
[1   0   1/2]
[0   1    0 ]
```

and its characteristic polynomial is `w(w²−1)`. At order one the matrix is `[0]`, giving `w`. At order five, `a₋₃=c₂=−1/8` enters on the third superdiagonal, and the polynomial is `w(w²−1)² = w⁵−2w³+w`. The negative `c₂` is a useful sign check.

## All-order finite algebra

Write `n=2m+1`. Reorder matrix coordinates as even indices `0,2,…,2m` followed by odd indices `1,3,…,2m−1`. The matrix has off-diagonal blocks `B : (m+1)×m` and `C : m×(m+1)`:

```text
Bᵢⱼ = c_(j+1−i),   0≤i≤m, 0≤j<m;
Cᵢⱼ = c_(j−i),     0≤i<m, 0≤j≤m,
```

with `c_r=0` for negative `r`. Let `G : (m+1)×(m+1)` be upper triangular Toeplitz, `Gᵢⱼ=c_(j−i)`, and let `U` be its upper unit shift. The square-root coefficient convolution gives `G²=I+U` exactly, with no limiting matrix argument. If `E` selects columns `1,…,m` and `P` selects rows `0,…,m−1`, then `B=GE`, `C=PG` and

```text
(CB)ᵢⱼ = Σₖ c_(k−i)c_(j+1−k)
        = 1 if i=j or i=j+1, and 0 otherwise.
```

Thus `CB` is an `m×m` unit lower bidiagonal matrix and `det(w²I_m−CB)=(w²−1)^m`. The characteristic polynomial of the odd off-diagonal block matrix is `w det(w²I_m−CB)`; this is a polynomial identity valid even at `w=0` and does not require diagonalizability. It yields the target for all `m`. The empty `m=0` block has determinant one, so the same formula gives `w`.

An implementation may factor this into separately proved Fourier, coefficient-convolution, block-reindexing, and determinant lemmas. Their final combination must use the actual `BaseSymbol` and frozen `Toeplitz`, with no assumed Fourier identity or charpoly axiom.

## Scope boundary

The base symbol has an exterior holomorphic branch and hence an outer annular extension; it fails the “neither extension” premise of the original conjecture. This polynomial identity alone cannot prove `SP14.Target`. The final source symbol includes positive and negative packets and finite corrections, whose multiplicity and extension properties remain separate obligations. No finite-order base computation is evidence for their infinite construction.
