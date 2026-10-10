# RA-10 compression eigenvalue comparison at the actual selected projector

**Status:** source-locked mathematical, indexing and numerical precontract for independent review. No Lean implementation or min-max theorem is claimed.

## Frozen source and prior gates

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `lean-statements/NLA/Proofs/RA10/SelectedProjectionIdempotent.lean` | `8ac0fb000300bca16bacdbefe1d0e8c4286418df8bc1c466081e6a1edf966a78` |
| `lean-statements/NLA/Proofs/RA10/MatchedLeadingSupport.lean` | `426403f51df54d1ffa70f839b18921da2a9b63ea265112213e8c66d2530c0c18` |
| `lean-statements/NLA/Proofs/RA10/SelectedCompressionOrderedSpectral.lean` | `d4ac007b8f7dbd53c1e107bd99a76ee30dbc70f189fea28fc71f91545fab0504` |

Source Section 3 takes an arbitrary rank-`k` selected projector `P` from the prescribed first `k` `QAhat` columns, defines `C=PAP`, and writes its `k` compression eigenvalues as `h₁≥⋯≥hₖ`. It asserts `0≤h_i≤a_i` for source **one-based** `1≤i≤k`, where `a_i` are eigenvalues of A. The frozen Lean sequences are indexed by `Fin n` from zero, so source `h_i` is `eigenvaluesC a` and source `a_i` is `eigenvaluesA a` with `a.val=i−1`, hence `a.val<k`. The source final target uses `1≤k<n`; the precontract permits all `k≤n`, including `k=0`, `k=n`, and `n=0`.

## Exact mathematics and proof obligation

Let `hA` and `hAhat` be the original independently supplied ordered PSD decompositions, let `P=selectedProjection k QAhat`, `C=PAP`, and let `hC` be **any** ordered PSD decomposition of this actual C, with sorted sequence `eigenvaluesC` and basis `QC`. The constructed decomposition gate ensures such an `hC` exists but does not make it unique; the comparison must hold for every supplied `hC`, including arbitrary bases within ties and zero eigenspaces. For every `a:Fin n` with `a.val<k`:

```text
0 ≤ eigenvaluesC a ≤ eigenvaluesA a.
```

The first inequality is already a conjunct of `hC`. The second is a compression eigenvalue/min-max comparison. It is **not** the false Loewner assertion `PAP≤A`; compression and A need not be ordered as matrices. The proof should use the supplied eigenbases and finite-dimensional subspace dimensions, with no numerical approximation:

1. `P²=P`, `Pᵀ=P`, and `P C P=C` hold for the exact selected `P`. Thus `P C=C`. If `C v=λv` with `λ>0`, then `λ P v=P C v=C v=λv`, so `P v=v`. In particular every C eigenvector among the first `a.val+1` indices is P-supported whenever `eigenvaluesC a>0`, because the sorted eigenvalues above it are at least that positive value.
2. Let `E_C(a)` be the span of the first `a.val+1` supplied `QC` eigenvectors. It has dimension `a.val+1`; if `eigenvaluesC a>0`, the entire span lies in `range(P)`. Let `F_A(a)` be the span of supplied `QA` eigenvectors from index `a.val` through `n−1`, of dimension `n−a.val`. These dimensions sum to `n+1`, so `E_C(a)∩F_A(a)` contains a nonzero real vector `v`, including all tie cases.
3. For this `v`, `Pv=v`, hence `vᵀCv=vᵀAv`. The exact spectral expansions give `vᵀCv≥eigenvaluesC a·‖v‖₂²` from the first C eigenspace and `vᵀAv≤eigenvaluesA a·‖v‖₂²` from the A tail eigenspace. Since `v≠0`, conclude `eigenvaluesC a≤eigenvaluesA a`. If `eigenvaluesC a=0`, the conclusion follows directly from `hA` nonnegativity.

All spans and dimensions are over `ℝ`; there is no basis reselection or ordering of QA/QAhat. For `k=0` and `n=0`, no index satisfies `a.val<k`; the theorem remains valid. For `k=n`, every source compression eigenvalue is included, and `P=I` by its `n` selected orthonormal columns, so equality is possible. Ties and zero eigenvalues require no strict spectral gap. The theorem's numerical target is the exact coefficient-one comparison, not a trace, nuclear, or L2 norm surrogate.

## Proposed exact Lean declarations

Use a new `NLA.Proofs.RA10.SelectedCompressionEigenvalue` module; import the frozen projector/support/spectral gates and pinned finite-dimensional inner-product-space APIs as needed. The first support helper is deliberately staged and retains source P and actual C. `Matrix.mulVec` uses `Fin n` columns and is not entrywise multiplication.

```lean
namespace NLA.Proofs.RA10

theorem selectedCompression_positiveEigenvector_supported {n k : ℕ}
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC)
    (a : Fin n) (ha : 0 < eigenvaluesC a) :
    let P := selectedProjection k QAhat
    let v : Fin n → ℝ := fun i => QC i a
    P *ᵥ v = v := by
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

Implementation may freeze the positive-eigenvector support helper first if the finite-dimensional intersection/min-max bridge needs more work. Such a stage must retain its own exact scope and cannot claim the eigenvalue comparison. Do not add a premise that already assumes the comparison, substitute an arbitrary PSD C, or infer it from `PAP≤A`.

## Independent review boundary

Check source's one-based-to-zero-based mapping, `k≤n` and empty cases, the actual `P=selectedProjection k QAhat` and `C=PAP`, universality over hC/tied bases, positivity-conditioned support step, dimension intersection and exact coefficient-one comparison. After approval, implement only kernel-proved stages with pinned Lean 4.33.1/LeanCert, freeze source SHA and request independent imported exact-signature/source/axiom audit. Source pinching/nuclear inequality (8), ridge compression Lemma 2, Equation (14)'s nuclear ideal inequality, arbitrary selected approximants, integral representation and full RA-10 Target remain open.
