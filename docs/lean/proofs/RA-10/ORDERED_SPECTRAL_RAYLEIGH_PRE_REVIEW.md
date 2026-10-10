# RA-10 exact Parseval and ordered spectral Rayleigh bounds

**Status:** source-locked mathematical/indexing/numerical precontract for independent review. No Lean implementation or compression min-max theorem is claimed.

## Frozen source and dependency

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `lean-statements/NLA/Proofs/RA10/SpectralQuadratic.lean` | `23e82984e32c8724fda21446037db91ca0180f52d41602dde086d16a1f954eae` |
| `lean-statements/NLA/Proofs/RA10/SelectedCompressionEigenvalue.lean` | `00c62e352faab14482b768bd95ceadbcb76ebb6a69e69ad2d6979376aa142d13` |

Source Section 3 compares the sorted compression eigenvalues `h_i` of the actual `C=PAP` against sorted eigenvalues `a_i` of A. The independently reviewed min-max precontract uses a nonzero vector in the span of the first `i` C eigenvectors and the tail of the supplied A eigenvectors. This gate establishes the **exact numerical Rayleigh bounds** on such vectors from the frozen spectral predicate. It is generic in a supplied ordered PSD decomposition and does not itself assert the intersection vector or `h_i≤a_i`.

## Exact finite-dimensional mathematics

Let `hM : OrderedPSDSpectralDecomposition M eigenvalues Q`, with `a : Fin n` zero based and arbitrary `x : Fin n→ℝ`. Define the actual supplied-basis coordinate

```text
coord_Q(x,b) := Σ_i x_i Q_i,b.
```

Because the `n` supplied columns of square Q are orthonormal, they are a complete orthonormal basis even for ties/zero eigenvalues, and the exact Parseval identity is

```text
Σ_i x_i² = Σ_b coord_Q(x,b)².
```

The approved spectral quadratic expansion is `xᵀMx=Σ_b eigenvalues(b)·coord_Q(x,b)²` with the frozen double sum `xᵀMx=Σ_iΣ_j x_i M_ij x_j`.

If all coordinates **after** `a` vanish (`a.val<b.val → coord_Q(x,b)=0`), then only `b≤a` remain and antitonicity gives `eigenvalues(b)≥eigenvalues(a)`. Since every coordinate square is nonnegative, the exact coefficient-one lower bound is

```text
eigenvalues(a) · Σ_i x_i² ≤ Σ_iΣ_j x_i M_ij x_j.
```

If all coordinates **before** `a` vanish (`b.val<a.val → coord_Q(x,b)=0`), then only `b≥a` remain and antitonicity gives `eigenvalues(b)≤eigenvalues(a)`. The exact coefficient-one upper bound is

```text
Σ_iΣ_j x_i M_ij x_j ≤ eigenvalues(a) · Σ_i x_i².
```

No positive eigenvalue, normalization of x, or spectral gap is assumed. Both statements hold with `x=0`, tied eigenvalues, zero eigenvalues, and `n=0` (there is no `a` when n=0). They are real scalar sum inequalities, not nuclear or L2 operator norm inequalities. Later, apply the lower bound to C and the upper bound to A on the same nonzero intersection vector to prove the source's one-based `h_i≤a_i` (`a.val=i−1` in Lean).

## Proposed exact Lean declarations

Use a separate `NLA.Proofs.RA10.OrderedSpectralRayleigh` module. The full frozen M and supplied Q remain; no eigenbasis is selected anew. These signatures use `a.val` explicitly to avoid off-by-one shifts.

```lean
namespace NLA.Proofs.RA10

theorem orderedPSDSpectral_parseval {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ} {eigenvalues : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (hM : NLA.Statements.RA10.OrderedPSDSpectralDecomposition M eigenvalues Q)
    (x : Fin n → ℝ) :
    (∑ i : Fin n, x i ^ 2) =
      ∑ b : Fin n, (∑ i : Fin n, x i * Q i b) ^ 2 := by
  ...

theorem orderedPSDSpectral_rayleigh_lower_prefix {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ} {eigenvalues : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (hM : NLA.Statements.RA10.OrderedPSDSpectralDecomposition M eigenvalues Q)
    (a : Fin n) (x : Fin n → ℝ)
    (hx : ∀ b : Fin n, a.val < b.val → (∑ i : Fin n, x i * Q i b) = 0) :
    eigenvalues a * (∑ i : Fin n, x i ^ 2) ≤
      ∑ i : Fin n, ∑ j : Fin n, x i * M i j * x j := by
  ...

theorem orderedPSDSpectral_rayleigh_upper_suffix {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ} {eigenvalues : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (hM : NLA.Statements.RA10.OrderedPSDSpectralDecomposition M eigenvalues Q)
    (a : Fin n) (x : Fin n → ℝ)
    (hx : ∀ b : Fin n, b.val < a.val → (∑ i : Fin n, x i * Q i b) = 0) :
    (∑ i : Fin n, ∑ j : Fin n, x i * M i j * x j) ≤
      eigenvalues a * (∑ i : Fin n, x i ^ 2) := by
  ...

end NLA.Proofs.RA10
```

The Parseval equality can be implemented/frozen as a first honest stage if the two order bounds require further finite-sum work. Do not claim either Rayleigh bound until the exact signature, including coordinate-zero premise and coefficient one, passes LeanCert kernel.

## Independent review boundary

Check Parseval for square orthonormal Q and `n=0`, the direction of antitone inequalities on prefix/suffix, precise strict coordinate cutoffs, the exact frozen double-sum quadratic form, ties/zero cases and coefficient one. After approval, implement with pinned Lean 4.33.1/LeanCert kernel, freeze source and request imported exact-signature/source/axiom audit. The nonzero intersection vector, compression eigenvalue comparison, source nuclear pinching, Lemma 2, Equation (14)'s nuclear ideal bound and full RA-10 Target remain open.
