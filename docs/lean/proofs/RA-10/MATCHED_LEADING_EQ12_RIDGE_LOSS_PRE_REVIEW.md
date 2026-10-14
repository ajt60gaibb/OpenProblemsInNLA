# RA-10 Eq. (12): exact ridge loss of the selected compression

**Status:** source-only mathematical, numerical, and indexing precontract for independent review. No Lean implementation is authorized by this document. This is a partial gate toward the unchanged RA-10 `Target`.

## Frozen sources and proved dependencies

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `lean-statements/NLA/Proofs/RA10/RidgeScalar.lean` | `5eab9a208a8fa9cb3f7c5cfa7ad0888ff3a0ac4c23f1236ee6166f6f1eaf792f` |
| `lean-statements/NLA/Proofs/RA10/SelectedCompressionComparison.lean` | `0d9d37901de4cca6e48f40d5a73740093b5e60bc9a0b7113cc2189de85013741` |
| `lean-statements/NLA/Proofs/RA10/SelectedCompressionTail.lean` | `bf7df719a1e84abfc819df5e43a61ea2392529560ffda11a94fdde43f418033b` |
| `lean-statements/NLA/Proofs/RA10/SelectedCompressionOrderedSpectral.lean` | `d4ac007b8f7dbd53c1e107bd99a76ee30dbc70f189fea28fc71f91545fab0504` |
| `lean-statements/NLA/Proofs/RA10/MatchedLeadingEq11Variational.lean` | `8aafb09c891e55d8de642cf5da0fd6c854ba3f9e2b50ecc4f5628ee790f46989` |

The frozen statement, ID, canonical README, and both independently supplied bases remain unchanged. Source Equation (12) is already proved at the scalar level by `ridgeAtom_abs_sub_eq` and `ridgeAtom_abs_sub_le`. The new gate is precisely its finite trace-sum consequence `0≤L_s≤gL` immediately following Equation (12) in the solution. It does not claim source Equation (13), full transfer, or the target.

## Exact mathematics and branch

Assume the source range `1≤k<n` and `s>0`. Set `P=selectedProjection k QAhat`, `C=P*A*P`, and `c=a_(k−1)=eigenvaluesA ⟨k−1,_⟩`. This gate handles the positive branch `c>0`; the frozen target makes no positivity assumption on `c`, so the zero branch must later be handled separately.

Take **any** ordered PSD spectral witness `(eigenvaluesC,QC)` of this actual `C`, independently of the frozen supplied `(eigenvaluesA,QA)` and `(eigenvaluesAhat,QAhat)`. Write `h_i=eigenvaluesC i`, `f_s(x)=ridgeAtom s x=x/(s+x)`, and

```text
S_top = ∑_{i.val<k} a_i,
L = S_top − tr C,
L_s = ∑_{i.val<k} f_s(a_i) − tr(FunctionMatrix f_s eigenvaluesC QC),
g = 1/(s+c).
```

The required exact conclusion is `0≤L_s≤gL`, with coefficient one. This is the source's `tr f_s(H)`: the full-space `FunctionMatrix f_s eigenvaluesC QC` equals the functional calculus of actual `C`; its trace is `Σ_i f_s(h_i)`. The audited rank/tail theorem gives `h_i=0` for `i.val≥k`, and **exactly** `f_s(0)=0`, so this trace equals `Σ_{i.val<k}f_s(h_i)` without any basis alignment at zero eigenvalues. Similarly `tr C=Σ_{i.val<k}h_i`.

For each `i.val<k`, orderedness gives `a_i≥c>0`; the audited selected-compression comparison gives `0≤h_i≤a_i`. Since `f_s` is increasing on `[0,∞)`, `0≤f_s(a_i)−f_s(h_i)`. The audited source Eq. (12) scalar inequality gives

```text
f_s(a_i)−f_s(h_i)
 = |f_s(a_i)−f_s(h_i)|
 ≤ |a_i−h_i|/(s+c)
 = (a_i−h_i)/(s+c).
```

Sum over exactly the zero-based prefix `i.val<k`. The trace identities then give `0≤L_s≤L/(s+c)=gL`. No eigenvalue gap, positive-tail condition, extra alignment of `QC`, or false Loewner inequality `C≤A` is used. Equal eigenvalues, zero `h_i`, `i=0`, and the empty tail are included. The source theorem's `1≤k<n` excludes `n=0`, while any private generic finite trace helper must handle `n=0` vacuously.

## Proposed exact public Lean signature

Implement in a new `NLA.Proofs.RA10.MatchedLeadingEq12RidgeLoss` module only after independent pre-review:

```lean
namespace NLA.Proofs.RA10

theorem matchedLeading_ridge_loss_nonneg_le {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QA QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC)
    {s : ℝ} (hs : 0 < s)
    (hc : 0 < eigenvaluesA ⟨k - 1, by omega⟩) :
    let c := eigenvaluesA ⟨k - 1, by omega⟩
    let C := selectedProjection k QAhat * A * selectedProjection k QAhat
    let L := (∑ i : Fin n, if i.val < k then eigenvaluesA i else 0) - Matrix.trace C
    let L_s := (∑ i : Fin n, if i.val < k then ridgeAtom s (eigenvaluesA i) else 0) -
      Matrix.trace (NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesC QC)
    0 ≤ L_s ∧ L_s ≤ L / (s + c) := by
  ...

end NLA.Proofs.RA10
```

The exact `let`-bound objects, every original basis, actual compression, positive-branch hypothesis, and denominator `s+c` are part of the proposed signature. Private finite trace and sum lemmas are permitted, but any new public signature needs a separate pre-review. After implementation, direct pinned LeanCert kernel checking, frozen SHA, separate imported exact-signature/source/axiom audit, and aggregate import are required. The final RA-10 target remains open.
