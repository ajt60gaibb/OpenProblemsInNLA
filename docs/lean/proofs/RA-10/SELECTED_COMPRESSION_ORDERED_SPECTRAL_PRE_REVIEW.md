# RA-10 sorted real spectral decomposition of the actual selected compression

**Status:** exact source-locked mathematical/indexing precontract for independent review. No Lean implementation or full transfer proof is claimed.

## Frozen source and pinned library

| Source | SHA-256 or revision |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `lean-statements/NLA/Proofs/RA10/CustomPSDMathlibBridge.lean` | `ca0e97485f3538275f12006d3619687d4c49bf0c1e7a8e2f698dadf87b64e0b7` |
| pinned Mathlib in `lean-statements/lake-manifest.json` | `0df444a360eaa60ab8c11dca51a86af692955474` |

Source Section 3 sets `P` to the first `k` supplied `QAhat` eigenvectors and `C=PAP`, then uses an ordered real spectral decomposition of this **actual** `C` in source Equation (14) and the compression eigenvalue comparison. The reviewed bridge proves `Matrix.PosSemidef C` in pinned Mathlib. This gate constructs a frozen `OrderedPSDSpectralDecomposition C λC QC`, thereby discharging the extra `hC` premise in the restricted Equation (14) equality. It does not compare λC to λA or prove the nuclear inequality.

## Exact spectral construction and indexing

For arbitrary finite `n` and a real `M : Matrix (Fin n) (Fin n) ℝ` with pinned `Matrix.PosSemidef M`, write `hHerm := hM.1`. Pinned Mathlib `Matrix.IsHermitian.eigenvalues₀ hHerm` is indexed by `Fin (Fintype.card (Fin n))`, is antitone by `eigenvalues₀_antitone`, and its unsorted-index companion `hHerm.eigenvalues` is paired with columns of `hHerm.eigenvectorUnitary`. Pinned `Matrix.PosSemidef.eigenvalues_nonneg` gives nonnegativity of each paired eigenvalue. The real `hHerm.spectral_theorem` reconstructs M from those columns and eigenvalues.

The library's `Fintype.equivOfCardEq (Fintype.card_fin n)` maps the sorted-index type to `Fin n`, but that arbitrary equivalence need **not** preserve order. Do **not** infer `Antitone hHerm.eigenvalues` directly. Instead use the order-preserving

```text
t : Fin n ≃o Fin (Fintype.card (Fin n))
  := Fin.castOrderIso (Fintype.card_fin n).symm,
e : Fin (Fintype.card (Fin n)) ≃ Fin n
  := Fintype.equivOfCardEq (Fintype.card_fin n),
σ : Fin n ≃ Fin n := t.toEquiv.trans e.
```

By pinned definitions, `hHerm.eigenvalues (σ a) = hHerm.eigenvalues₀ (t a)` for each `a`. Thus `λC a := hHerm.eigenvalues (σ a)` is antitone because `t` preserves order and `eigenvalues₀` is antitone. Define `QC i a := (hHerm.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) i (σ a)`. This reindexes **both** eigenvalues and columns by the same bijection; it does not alter their pairing or choose a new basis for A/Ahat. Its columns are orthonormal and the pinned spectral theorem plus a bijective finite sum reindex proves the exact frozen reconstruction

```text
M_ij = Σ_a λC a · QC_i,a · QC_j,a.
```

Together with `λC a≥0`, this is precisely all four conjuncts of `OrderedPSDSpectralDecomposition M λC QC`: nonnegativity, antitonicity, column orthonormality, and equality to `SpectralMatrix λC QC`. When eigenvalues tie, σ still reindexes their paired columns and the supplied `QAhat` is untouched. Zero eigenvalues remain present. For `n=0`, all index types are empty, the unique equivalences and empty sums satisfy every conjunct. There is no implicit rank or positive-definiteness premise.

Finally apply the generic result to `M=C=PAP` using the kernel-proved `selectedCompression_mathlibPosSemidef hA hAhat`. The existential witnesses are an additional **constructed** basis `QC` and sequence λC for the compression; the original quantified `QA` and `QAhat` in the frozen target remain independently supplied and unchanged. The source's later numerical claim `0≤h_i≤a_i` is **not** established here; it requires a separate min-max proof.

## Proposed exact Lean declarations

Use new `NLA.Proofs.RA10.SelectedCompressionOrderedSpectral` module. Import pinned `Mathlib.Analysis.Matrix.PosDef`, which imports the real Hermitian spectral theorem. The helper `sortedHermitianIndex` records the exact common eigenvalue/column reindex above. If elaboration requires a simpler definitional cast, it must be separately shown order preserving and preserve the same pairing; no arbitrary `Fin n ≃ Fin n` may be treated as order preserving.

```lean
namespace NLA.Proofs.RA10

noncomputable def sortedHermitianIndex (n : ℕ) : Fin n ≃ Fin n :=
  (Fin.castOrderIso (Fintype.card_fin n).symm).toEquiv.trans
    (Fintype.equivOfCardEq (Fintype.card_fin n))

theorem mathlibPosSemidef_sortedEigenvalues_antitone {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : Matrix.PosSemidef M) :
    Antitone (fun a : Fin n => hM.1.eigenvalues (sortedHermitianIndex n a)) := by
  ...

theorem mathlibPosSemidef_exists_orderedPSD {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : Matrix.PosSemidef M) :
    ∃ (eigenvalues : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ),
      NLA.Statements.RA10.OrderedPSDSpectralDecomposition M eigenvalues Q := by
  ...

theorem selectedCompression_exists_orderedPSD {n k : ℕ}
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat) :
    ∃ (eigenvaluesC : Fin n → ℝ) (QC : Matrix (Fin n) (Fin n) ℝ),
      NLA.Statements.RA10.OrderedPSDSpectralDecomposition
        (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC := by
  ...

end NLA.Proofs.RA10
```

Staged implementation is permitted only with precise scope: the sorted-index and antitonicity helper may be frozen separately if full spectral reconstruction is not yet kernel proved. Do not label such a stage as `mathlibPosSemidef_exists_orderedPSD` or `selectedCompression_exists_orderedPSD` until the complete exact conjuncts pass LeanCert kernel.

## Independent review boundary

Verify the exact source compression and that this theorem constructs only its hC, the `Fin n` versus `Fin (card (Fin n))` order issue and common permutation σ, all four frozen spectral conjuncts, tied/zero and `n=0` cases, and the absence of a min-max or nuclear claim. Implementation follows only after independent approval, then pinned Lean 4.33.1/LeanCert kernel direct check, frozen source SHA and independent imported exact-signature/source/axiom audit. Source Lemma 2, pinching, min-max, Equation (14)'s nuclear ideal inequality, integral representation and the full RA-10 Target remain open.
