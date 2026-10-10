# RA-10 exact selected-compression eigenvalue comparison bridge

**Status:** source-locked mathematical, indexing and numerical precontract for independent review. No Lean implementation or claim about the full RA-10 target is made here.

## Frozen source and prerequisite gates

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `lean-statements/NLA/Proofs/RA10/SelectedProjectionBasic.lean` | `cfda9a5c7a4681542e47c967d5a4011e42b28f7cb3891bd3d192a7d336bea22b` |
| `lean-statements/NLA/Proofs/RA10/SelectedCompressionEigenvalue.lean` | `00c62e352faab14482b768bd95ceadbcb76ebb6a69e69ad2d6979376aa142d13` |
| `lean-statements/NLA/Proofs/RA10/OrderedSpectralRayleigh.lean` | `3a7c03df2db70a97f16fcf05a00585e3f25d10fc523c27f2a3c31a6f9c1a4fc8` |
| `lean-statements/NLA/Proofs/RA10/OrderedSpectralIntersection.lean` | `7f0b889dcc02b9d17ed8974fb639b313b6364615eeab3f0c3fb83446adec348d` |
| `lean-statements/NLA/Proofs/RA10/SelectedCompressionPrefixSupport.lean` | `96769da49e4b10fff8a47ababb707a0d7ea8e8de709fb490e16ad7bce526bb8c` |

The earlier independent pre-review `SELECTED_COMPRESSION_EIGENVALUE_PRE_REVIEW.md` (SHA `416765e812e37b58ffa2ca213e84572aff0f1224e1b7d64aed675ac1fc9ac5fb`) approved the full target signature and dimension-intersection argument. This contract makes the final quadratic and numerical steps explicit before any implementation. Section 3 of the original solution states source one-based `0≤h_i≤a_i` for `1≤i≤k` for the actual `C=PAP`, with `P` the first-`k` projector from the supplied `QAhat`. Here source `i` is Lean `a.val+1`, and `a.val<k≤n` is exact.

## Exact algebraic and numerical claims

Let `P=selectedProjection k QAhat` and `C=P*A*P`, where multiplication associates left: `(P*A)*P`. The frozen selected projection is symmetric: `Pᵀ=P`. For any real A (PSD is unnecessary for this algebra) and vector x with `P*ᵥx=x`,

```text
Σ_i Σ_j x_i C_ij x_j = Σ_i Σ_j x_i A_ij x_j.
```

Indeed `(Px)ᵀ A(Px)=xᵀAx`; both factors of P must be used. This is an equality of the **same frozen double sums** used by `PositiveSemidefinite` and the Rayleigh gates, with no trace, L2 operator norm, or nuclear-norm surrogate.

For any nonzero real vector x in `Fin n→ℝ`, `Σ_i x_i²>0`. This follows because every square is nonnegative and at least one coordinate is nonzero. It is needed to cancel the common factor without dividing by zero. The statement is vacuous for `n=0`.

Now take any original `hA`, `hAhat`, and any supplied `hC` for the **actual** C. For `a.val<k≤n`, `hC` gives `0≤eigenvaluesC a`. If this value is zero, `hA` gives `0≤eigenvaluesA a`. If positive, use the separately proved intersection gate on the supplied `QC,QA` to get one nonzero x whose C coordinates vanish for `b>a` and A coordinates vanish for `b<a`. The positive-prefix support gate gives `Px=x`. The exact quadratic equality above and the exact Rayleigh inequalities then give

```text
eigenvaluesC a * Σ_i x_i²
  ≤ Σ_iΣ_j x_i C_ij x_j
  = Σ_iΣ_j x_i A_ij x_j
  ≤ eigenvaluesA a * Σ_i x_i².
```

Since `Σ_i x_i²>0`, the exact **coefficient-one** bound is `eigenvaluesC a≤eigenvaluesA a`, with no additive error or dimension factor. Ties, positive and zero eigenspaces, arbitrary supplied bases, `k=n`, and the empty `k=0`/`n=0` cases are all included; no spectral gap or basis alignment is assumed. The final RA-10 TransferBound uses `1≤k<n`, a subset of this gate's `k≤n` regime.

## Proposed exact Lean declarations

Create a separate `NLA.Proofs.RA10.SelectedCompressionComparison` module importing the frozen intersection, positive-prefix, Rayleigh and selected-projection gates. The final theorem repeats the exact approved signature from the previous eigenvalue pre-review; it must not replace actual C by an arbitrary PSD matrix. The first two declarations may be frozen as honest stages if the final comparison proof takes longer.

```lean
namespace NLA.Proofs.RA10

theorem selectedCompression_supported_quadratic_eq {n k : ℕ}
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesAhat : Fin n → ℝ}
    {QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (x : Fin n → ℝ)
    (hx : selectedProjection k QAhat *ᵥ x = x) :
    (∑ i : Fin n, ∑ j : Fin n,
      x i * (selectedProjection k QAhat * A * selectedProjection k QAhat) i j * x j) =
      ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j := by
  ...

theorem nonzero_vector_sum_sq_pos {n : ℕ} (x : Fin n → ℝ) (hx : x ≠ 0) :
    0 < ∑ i : Fin n, x i ^ 2 := by
  ...

theorem selectedCompression_eigenvalues_nonneg_le {n k : ℕ}
    (hk : k ≤ n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QA QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC)
    (a : Fin n) (ha : a.val < k) :
    0 ≤ eigenvaluesC a ∧ eigenvaluesC a ≤ eigenvaluesA a := by
  ...

end NLA.Proofs.RA10
```

The nonzero intersection vector must be used *once* in both Rayleigh bounds. No use of the false Loewner assertion `PAP≤A` is permitted. A theorem proving the same final inequality with `hk`/`ha` unused internally is acceptable because that would be mathematically stronger while retaining this exact reviewed public signature and all source quantifiers.

## Independent review boundary

Check left-associated C=PAP, both P insertions, P symmetry, exact double-sum quadratic equality, strict positivity of the squared norm, one-based-to-zero-based mapping, the positive/zero cases and coefficient-one cancellation. Check that every supplied `QA`, `QAhat`, `QC` remains the original input and hC is universally quantified over decompositions of actual C. After approval, use pinned Lean 4.33.1/LeanCert kernel, freeze each proved stage/source SHA, and request independent imported exact-signature/source/axiom audit. This comparison alone does not prove source nuclear pinching (8), Lemma 2, Equation (14)'s nuclear ideal bound, arbitrary selected approximants, integral representation, or the full RA-10 Target.
