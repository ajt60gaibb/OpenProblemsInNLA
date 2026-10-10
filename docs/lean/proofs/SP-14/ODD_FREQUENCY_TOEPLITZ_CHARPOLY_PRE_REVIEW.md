# SP-14 odd-frequency Toeplitz characteristic polynomial: pre-proof contract

**Author:** `/root/sp14_base_proof`, 10 October 2026. **Status:** frozen for independent mathematical and Lean-signature review before implementation. This finite lemma formalizes only the “no division ambiguity” statement in “Exact selection and the infinite symbol” of `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex` (SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`). The frozen original statement is `lean-statements/NLA/Statements/SP14.lean` (SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`). Permanent problem identity and the negative `Target` remain unchanged.

## Exact support condition and blocks

The support hypothesis concerns the **frozen real-interval integral** `NLA.Statements.SP14.FourierCoefficient`:

```lean
def OddFourierSupport (a : Circle → ℂ) : Prop :=
  ∀ p : ℤ, FourierCoefficient a (2 * p) = 0
```

No continuity hypothesis is needed for the finite algebra once these actual coefficients are supplied. The future source-specific proof that `a(z)=z g(z²)` with its continuous infinite series and finite packets satisfies `OddFourierSupport` is a separate obligation; the formal lemma must not infer it from the notation alone.

For `m:ℕ`, index even rows and columns by `Fin (m+1)` and odd rows and columns by `Fin m`. Set the rectangular blocks exactly to the row-minus-column entries of the frozen Toeplitz matrix:

```lean
noncomputable def oddB (a : Circle → ℂ) (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin m) ℂ :=
  fun i j => FourierCoefficient a
    ((2 * (i.val : ℤ)) - (2 * (j.val : ℤ) + 1))

noncomputable def oddC (a : Circle → ℂ) (m : ℕ) :
    Matrix (Fin m) (Fin (m + 1)) ℂ :=
  fun i j => FourierCoefficient a
    ((2 * (i.val : ℤ) + 1) - 2 * (j.val : ℤ))

noncomputable def oddQuotient (a : Circle → ℂ) (m : ℕ) : Polynomial ℂ :=
  (oddC a m * oddB a m).charpoly

noncomputable def oddJetPolynomial (a : Circle → ℂ) (m : ℕ) : Polynomial ℂ :=
  (oddQuotient a m).comp (Polynomial.X + 1)
```

The dimensions are important: `oddB : (m+1)×m`, `oddC : m×(m+1)`, so `oddC * oddB` is the `m×m` matrix whose characteristic polynomial is the explicit quotient `Q_m` below. The existing independently audited `baseParityEquiv m` is an equivalence from `Fin (m+1) ⊕ Fin m` to `Fin (2m+1)`. Use it to prove these exact all-order claims:

```lean
theorem toeplitz_odd_parity_blocks (a : Circle → ℂ) (m : ℕ)
    (hOdd : OddFourierSupport a) :
  Matrix.reindex (baseParityEquiv m).symm (baseParityEquiv m).symm
      (Toeplitz a (2 * m + 1)) =
    Matrix.fromBlocks 0 (oddB a m) (oddC a m) 0

theorem toeplitz_odd_charpoly (a : Circle → ℂ) (m : ℕ)
    (hOdd : OddFourierSupport a) :
  (Toeplitz a (2 * m + 1)).charpoly =
    Polynomial.X * (oddQuotient a m).comp (Polynomial.X ^ 2)

theorem toeplitz_odd_charpoly_in_jet (a : Circle → ℂ) (m : ℕ)
    (hOdd : OddFourierSupport a) :
  (Toeplitz a (2 * m + 1)).charpoly =
    Polynomial.X * (oddJetPolynomial a m).comp (Polynomial.X ^ 2 - 1)
```

The last equality is the exact polynomial substitution `t=w²−1`: if `Q_m(u)=charpoly(oddC*oddB)(u)`, then `R_m(t)=Q_m(t+1)` and `w Q_m(w²)=w R_m(w²−1)`. It shows that dividing the odd-order characteristic polynomial by `w` produces a genuine polynomial in `w²` and in the source's jet coordinate `t`. It does **not** divide by a value of `w`, nor assume `w≠0`.

## Proof and endpoint checks

With `hOdd`, the even/even and odd/odd parity blocks vanish: their row-minus-column frequency is twice an integer. The off-diagonal blocks are `oddB` and `oddC` by their definitions. Preserve the actual `Toeplitz` row-minus-column sign and `baseParityEquiv` indexing; do not transpose `oddB`/`oddC` or change the Fourier convention. Reindexing preserves characteristic polynomials. Then apply the audited `charpoly_offdiagonal_succ` to obtain `X * charpoly(oddC*oddB).comp(X²)` for every `m`, including `m=0`, and including the polynomial value at `X=0`. Polynomial composition yields the jet-coordinate equality.

At `m=0`, the Toeplitz section is `1×1`, its sole diagonal coefficient is zero by `hOdd p=0`, and the lower block is empty. `oddQuotient a 0=1`, so both displayed characteristic-polynomial formulas reduce to `X`. At `m=1`, the parity order is `(0,2;1)`, `oddB` has shape `2×1`, and `oddC` has shape `1×2`; the product is `1×1`, not `2×2`. No normality, diagonalizability, finite Laurent support, or parameter regularity is assumed.

## Scope and remaining source obligations

This is a generic finite algebra consequence of the **assumed exact even-frequency vanishing**. It does not prove that the corrected infinite symbol has that support, that any first `h` coefficients of `oddJetPolynomial` vanish, that the polynomial equations in the selected `v_d` have regular roots, or that `±1` have positive asymptotic algebraic multiplicity. It also does not construct the final continuous symbol, prove either one-sided nonextension, or exhibit the canonical-versus-empirical gap required by `Target`. The base exterior symbol has an outer extension and is not the final counterexample.
