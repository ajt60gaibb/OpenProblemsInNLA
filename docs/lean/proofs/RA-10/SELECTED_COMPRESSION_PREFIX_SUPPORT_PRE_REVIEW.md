# RA-10 positive compression prefix lies in the actual selected projector range

**Status:** source-locked mathematical/indexing precontract for independent review. No Lean implementation or compression eigenvalue comparison is claimed.

## Frozen source and completed dependencies

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `lean-statements/NLA/Proofs/RA10/SelectedCompressionEigenvalue.lean` | `00c62e352faab14482b768bd95ceadbcb76ebb6a69e69ad2d6979376aa142d13` |
| `lean-statements/NLA/Proofs/RA10/OrderedSpectralRayleigh.lean` | `3a7c03df2db70a97f16fcf05a00585e3f25d10fc523c27f2a3c31a6f9c1a4fc8` |
| `lean-statements/NLA/Proofs/RA10/OrderedSpectralIntersection.lean` | `7f0b889dcc02b9d17ed8974fb639b313b6364615eeab3f0c3fb83446adec348d` |

The original Section 3 compression is `C=PAP` for the rank-`k` projector onto the **supplied** first `k` `QAhat` columns. Source one-based `h_i≤a_i` maps to zero-based `a : Fin n`, `a.val<k`. The separately approved comparison argument needs to show that the nonzero intersection vector from the preceding gate satisfies `P *ᵥ x=x` when `eigenvaluesC a>0`. The earlier exact helper proves this only for each **single** positive C eigenvector. This gate extends it to every vector with supplied `QC` coordinates in the prefix through `a`, with no basis reselection.

## Exact mathematics and indexing

For any `hM : OrderedPSDSpectralDecomposition M λ Q`, square-column orthonormality gives `QᵀQ=I` and `QQᵀ=I`, including `n=0`. Define `coord_Q(x,b)=Σ_i x_i Q_i,b`. Matrix multiplication gives the exact expansion

```text
x_i = Σ_b coord_Q(x,b) Q_i,b
```

for every `x : Fin n→ℝ` and `i : Fin n`. This statement is algebraic and retains the supplied Q; it does not require distinct or positive eigenvalues.

Now let `P=selectedProjection k QAhat` and let `hC` be **any** ordered PSD decomposition of the actual `C=PAP`, with supplied basis `QC`. Let `a : Fin n` satisfy `0<eigenvaluesC a`. Antitonicity gives `0<eigenvaluesC b` whenever `b.val≤a.val`, even across ties. The frozen positive-eigenvector helper proves `P *ᵥ QC.col b=QC.col b` for every such b. If `coord_QC(x,b)=0` whenever `a.val<b.val`, the complete-basis expansion uses only these supported columns, so linearity gives `P *ᵥ x=x`. There is no assumption about `a.val<k` in this conditional gate; for `k=0` and actual C=0, positive `eigenvaluesC a` is impossible, while for `k≥n`, P is I. For `n=0`, no a exists. Zero eigenvalues elsewhere and arbitrary tie bases are permitted.

## Proposed exact Lean declarations

Create a new `NLA.Proofs.RA10.SelectedCompressionPrefixSupport` module, importing the frozen spectral and positive-eigenvector gates. The first theorem is a reusable exact reconstruction and may be frozen as a stage if the second proof needs more work. The second theorem must retain both `hAhat` and the **actual** `C=PAP`, not an arbitrary PSD C or a newly chosen basis.

```lean
namespace NLA.Proofs.RA10

theorem orderedPSDSpectral_reconstruct_vector {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ} {eigenvalues : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (hM : NLA.Statements.RA10.OrderedPSDSpectralDecomposition M eigenvalues Q)
    (x : Fin n → ℝ) (i : Fin n) :
    x i = ∑ b : Fin n, (∑ j : Fin n, x j * Q j b) * Q i b := by
  ...

theorem selectedCompression_positivePrefix_supported {n k : ℕ}
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC)
    (a : Fin n) (ha : 0 < eigenvaluesC a)
    (x : Fin n → ℝ)
    (hx : ∀ b : Fin n, a.val < b.val → (∑ i : Fin n, x i * QC i b) = 0) :
    selectedProjection k QAhat *ᵥ x = x := by
  ...

end NLA.Proofs.RA10
```

The exact strict suffix cutoff is the one returned by `orderedSpectral_prefix_suffix_nonzero_intersection` and used by `orderedPSDSpectral_rayleigh_lower_prefix`. The claim does not require the intersection witness to be normalized and does not divide by an eigenvalue or introduce a spectral gap; the positive-eigenvector helper already handles positivity for each column.

## Independent review boundary

Check the square orthonormal reconstruction, supplied basis identity, positivity transfer `b≤a`, exact `P=selectedProjection k QAhat` and `C=PAP`, zero and tie cases, and equality of vectors rather than only a quadratic relation. After approval, implement only kernel-proved stages with pinned Lean 4.33.1/LeanCert and request separate imported exact-signature/source/axiom audit. The nonzero intersection and Rayleigh bounds are completed dependencies, but the quadratic equality, norm positivity/cancellation, source compression comparison, nuclear pinching, Lemma 2, Equation (14)'s nuclear ideal bound, and full RA-10 Target remain open.
