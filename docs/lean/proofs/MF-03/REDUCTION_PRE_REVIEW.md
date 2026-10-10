# MF-03 generic reduction: pre-proof contract

## Frozen target and scope

The target definition remains `NLA.Statements.MF03.ReducedPadeRepresentation` in
`lean-statements/NLA/Statements/MF03.lean`. The proposed implementation will be
in a new `lean-statements/NLA/Proofs/MF03/Reduction.lean` module. It will not
modify the target, existing proof modules, or CI/metadata.

Input SHA-256 hashes at review time:

- `lean-statements/NLA/Statements/MF03.lean`:
  `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24`
- `lean-statements/NLA/Proofs/MF03/Uniqueness.lean`:
  `c781644e76a6143535a45862263e6776ee1257ff6ac2d69eed328dd63f73daa5`

Proposed public Lean statement, in namespace `NLA.Proofs.MF03`:

```lean
theorem normalized_exists_reduced
    (m : ℕ) (P Q : Polynomial ℂ)
    (h : NLA.Statements.MF03.NormalizedPadeRepresentation m P Q) :
    ∃ Pᵣ Qᵣ : Polynomial ℂ,
      NLA.Statements.MF03.ReducedPadeRepresentation m Pᵣ Qᵣ ∧
        Pᵣ * Q = P * Qᵣ
```

The cross-product identity records the unchanged rational approximant without
dividing at possible roots. Its orientation matches the proposed statement.

## Algebraic construction

Let `D = gcd P Q`, `P₁ = P / D`, and `Q₁ = Q / D` in the Euclidean domain
`Polynomial ℂ`. The normalized hypothesis gives `Q.eval 0 = 1`, hence `Q ≠ 0`.
The gcd divides both inputs, and `D ≠ 0`, so `P = D * P₁` and `Q = D * Q₁`.
Evaluation of the second equality at zero gives
`D.eval 0 * Q₁.eval 0 = 1`, hence `D.eval 0 ≠ 0`.

Set `c = D.eval 0`, `Pᵣ = Polynomial.C c * P₁`, and
`Qᵣ = Polynomial.C c * Q₁`. Then `Qᵣ.eval 0 = c * Q₁.eval 0 = 1`.
The standard degree bound for a divisor of a nonzero polynomial, or degree
additivity for the displayed products, gives `P₁.natDegree ≤ m` and
`Q₁.natDegree ≤ m`. In fact the `j=0` equation forces `P.eval 0 = 1`, so
`P ≠ 0` under this theorem's hypotheses. Multiplication by a constant does
not increase natural degree.
The gcd quotient theorem `isCoprime_div_gcd_div_gcd` gives
`IsCoprime P₁ Q₁` from `Q ≠ 0`; multiplication of either argument by the
unit `Polynomial.C c` preserves coprimeness. Commutativity and the two
factorization identities yield `Pᵣ * Q = P * Qᵣ`.

The coefficient equation at `j=0` also gives `P.eval 0 = 1`, though the
construction only needs `Q.eval 0 = 1` to handle the nonzero cases.

## Coefficient preservation, including degree `2*m`

Define the formal series `F = PowerSeries.mk (fun j =>
1 / ((2*j).factorial : ℂ))`. The original finite-convolution equations are
equivalent to

```text
∀ j ≤ 2*m, coeff j ((Q : PowerSeries ℂ) * F - (P : PowerSeries ℂ)) = 0.
```

Using the quotient identities and polynomial-to-power-series coercion, the
series on the left equals

```text
(D : PowerSeries ℂ) *
  ((Q₁ : PowerSeries ℂ) * F - (P₁ : PowerSeries ℂ)).
```

For each `j ≤ 2*m`, induction on `j` in the formal-series product formula
gives the vanishing of the coefficient of the parenthesized series. The
`i=0` summand is `D.coeff 0` times its coefficient at `j`; all summands
with `i>0` contain a coefficient at an index `<j` and vanish by induction.
Since `D.coeff 0 = D.eval 0 = c ≠ 0`, the remaining coefficient is zero.
The induction includes the endpoint `j=2*m`; no limit or analytic result is
used. Multiplying both quotient polynomials by `Polynomial.C c` scales each
coefficient equation by `c`, giving the normalized Padé conditions for
`Pᵣ,Qᵣ`.

## Verification boundary

No axioms, `sorry`, or unproved numerical assumptions may enter the module.
The module must build in LeanCert kernel trust mode. The existing finite-order
certificates and disk transport theorem are independent of this lemma and are
not changed by this work.
