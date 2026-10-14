# RA-10 source Equation (11): positive-part defect bounded by trace loss

**Status:** source-locked mathematical, numerical, and indexing precontract for independent review. No Eq. (11) Lean declaration has been implemented. Permanent ID RA-10, its canonical README, the frozen `NLA.Statements.RA10.Target`, and the independently supplied `QA` and `QAhat` remain unchanged.

## Source and dependency locks

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `lean-statements/NLA/Proofs/RA10/SelectedProjectionRank.lean` | `71b13af889493c08dcadb56c749f049cfa34d939e602d8145c3a91de8ac15eb2` |
| `lean-statements/NLA/Proofs/RA10/SelectedProjectionIdempotent.lean` | `8ac0fb000300bca16bacdbefe1d0e8c4286418df8bc1c466081e6a1edf966a78` |
| `lean-statements/NLA/Proofs/RA10/SelectedCompressionPSD.lean` | `ad69432066d88ff06bbdc68c1841498c4355eb5569cbb5c976745b98f90b9222` |
| `lean-statements/NLA/Proofs/RA10/SelectedCompressionOrderedSpectral.lean` | `d4ac007b8f7dbd53c1e107bd99a76ee30dbc70f189fea28fc71f91545fab0504` |
| `lean-statements/NLA/Proofs/RA10/SelectedCompressionComparison.lean` | `0d9d37901de4cca6e48f40d5a73740093b5e60bc9a0b7113cc2189de85013741` |
| `lean-statements/NLA/Proofs/RA10/HermitianPositivePart.lean` | `db272c38e076cd0e41a278d9a488f5aba5cab71f1104f146236f591a8ef3f6e8` |
| `lean-statements/NLA/Proofs/RA10/MatchedLeadingEq10.lean` | `f0b3aa5c553138d8358c16c4a944d50b0c6d392abbb0d0686af11cec1c488be2` |

## Exact source objects

Fix the original two independent ordered PSD decompositions `hA` of `A` and `hAhat` of `Ahat`, with no equality assumed between `QA` and `QAhat`. In the source range `1 ≤ k < n`, set `P = selectedProjection k QAhat`, `C = P*A*P`, and `c = eigenvaluesA ⟨k−1, _⟩`. The source's one-based `a_k` is this zero-based `a_(k−1)`. Define the top trace loss

```
L = (∑ i : Fin n, if i.val < k then eigenvaluesA i else 0) − trace C.
```

The source defines `H=C` restricted to the `k`-dimensional range of `P` and

```
d = trace ((c I_k − H)₊).
```

On the full `Fin n` space the **same number** is `trace (hermitianPositivePart (c • P − C))`: the displayed matrix vanishes on `range(P)⊥`, and its restriction is exactly `c I_k−H`. This is a matrix spectral positive part, not an entrywise maximum. The final Lean theorem must use that exact matrix trace, or explicitly prove the equality to it before substituting a coordinate sum.

## Spectral indexing and rank gate

Let an arbitrary supplied `hC` be an `OrderedPSDSpectralDecomposition C eigenvaluesC QC`; its existence is already kernel-proved for the actual `C`. Since `P` is an orthogonal rank-`k` projector and `C=PCP`, `rank C≤k`. The ordered nonnegative spectral decomposition therefore has `eigenvaluesC i=0` whenever `k≤i.val`; otherwise at least `k+1` positive eigenvalues would force `rank C≥k+1`. Thus, including any ties at zero,

```
trace C = ∑ i : Fin n, if i.val < k then eigenvaluesC i else 0.
```

This must be proved for every such `hC`, not by choosing an eigenbasis aligned with `QAhat`. It remains true at `k=0`, `k=n`, and `n=0` where the corresponding tails are empty. The existing coefficient-one comparison gives `0≤h_i:=eigenvaluesC i≤a_i:=eigenvaluesA i` for `i.val<k`.

For every `i.val<k`, the original `a_i` is at least `c=a_(k−1)` by antitonicity of `eigenvaluesA`. Consequently the **pointwise coefficient-one** inequality is

```
max(c − h_i, 0) ≤ a_i − h_i.
```

If `c−h_i≥0`, use `c≤a_i`; otherwise use `h_i≤a_i`. It holds for ties, zeros, singular `H`, and `c=0`. Summing and using the trace-prefix identity gives

```
∑ i : Fin n, (if i.val < k then max(c − eigenvaluesC i, 0) else 0) ≤ L.
```

The remaining matrix identification is precise: because `C=PCP`, `P=Pᵀ=P²`, and `C` is PSD, `P` and `C` commute. On `range P`, the eigenvalues of `cP−C` are exactly `c−h_0,…,c−h_(k−1)` with multiplicities; on the complement they are zero. Hence

```
trace (hermitianPositivePart (c • P − C))
  = ∑ i : Fin n, (if i.val < k then max(c − eigenvaluesC i, 0) else 0).
```

One proof may select an orthonormal eigenbasis of `C` whose positive-eigenvalue vectors lie in `range P`, then extend its zero-eigenspace basis to split `range P` and `range P⊥`; zero eigenvalue ties must not be used to silently identify the given `QC` with `QAhat`. An equivalent finite-dimensional spectral/functional-calculus proof is acceptable. The numerical equality itself, including multiplicity at zero, is required before claiming source `d`.

## Proposed staged Lean signatures

Use separate kernel-audited modules if needed. First rank/trace; then the scalar sum bound; finally the full matrix positive-part defect. The first two gates do not imply the third without the exact spectral identification above.

```lean
namespace NLA.Proofs.RA10

theorem selectedCompression_eigenvalues_tail_zero {n k : ℕ}
    (hk : k ≤ n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC)
    (i : Fin n) (hi : k ≤ i.val) :
    eigenvaluesC i = 0 := by
  ...

theorem selectedCompression_trace_prefix {n k : ℕ}
    (hk : k ≤ n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC) :
    Matrix.trace (selectedProjection k QAhat * A * selectedProjection k QAhat) =
      ∑ i : Fin n, if i.val < k then eigenvaluesC i else 0 := by
  ...

theorem matchedLeading_defect_sum_le_loss {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QA QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC) :
    let c := eigenvaluesA ⟨k - 1, by omega⟩
    let P := selectedProjection k QAhat
    let C := P * A * P
    let L := (∑ i : Fin n, if i.val < k then eigenvaluesA i else 0) - Matrix.trace C
    (∑ i : Fin n, if i.val < k then max (c - eigenvaluesC i) 0 else 0) ≤ L := by
  ...

theorem matchedLeading_defect_positivePart_eq_sum {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QA QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC) :
    let c := eigenvaluesA ⟨k - 1, by omega⟩
    let P := selectedProjection k QAhat
    let C := P * A * P
    Matrix.trace (hermitianPositivePart (c • P - C)) =
      ∑ i : Fin n, if i.val < k then max (c - eigenvaluesC i) 0 else 0 := by
  ...

theorem matchedLeading_defect_le_loss {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat) :
    let c := eigenvaluesA ⟨k - 1, by omega⟩
    let P := selectedProjection k QAhat
    let C := P * A * P
    let L := (∑ i : Fin n, if i.val < k then eigenvaluesA i else 0) - Matrix.trace C
    Matrix.trace (hermitianPositivePart (c • P - C)) ≤ L := by
  ...

end NLA.Proofs.RA10
```

The `by omega` proof of the `Fin n` cast is an indexing witness only; no theorem may alter `c`, the strict cut, or either supplied basis. The source Section 3 assumes `τ>0`, hence `c>0`, but Eq. (11)'s scalar inequality and matrix identity extend to `c=0`; keeping the frozen `1≤k<n` regime is enough and avoids an artificial extra positivity hypothesis. The full source Lemma 2, Eqs. (12)–(17), and RA-10 Target remain open.
