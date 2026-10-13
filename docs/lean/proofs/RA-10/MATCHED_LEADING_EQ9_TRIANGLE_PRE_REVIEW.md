# RA-10 source Equation (9): exact compression excess triangle

**Status:** source-locked mathematical/numerical/indexing precontract for independent review. No Lean implementation of the proposed theorem is claimed. The permanent RA-10 ID, canonical README, frozen `NLA.Statements.RA10.Target`, and its original supplied bases/quantifiers remain unchanged.

## Source and dependencies

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `lean-statements/NLA/Proofs/RA10/NuclearNormTriangle.lean` | `aa58d4301953e3ead89eff907d0f02f3d5e88fe7d530d06fa7de5d844e40614f` |
| `lean-statements/NLA/Proofs/RA10/MatchedLeadingEq8.lean` | `d9385bc8281ce98fe910f9258f6b3d1e958d73eac98687b726205914659f9bff` |

Source Section 3 defines `B₀` using the first `k` eigenvalues of `A` but the selected eigenvectors of `Ahat`, `P` from that same supplied selected basis, `C=PAP`, and the zero-based best-rank tail `τ=Σ_{k≤i.val} aᵢ`. It sets `e₀=NuclearNorm(A−B₀)−τ`, `e_C=NuclearNorm(A−C)−τ`, and `R=NuclearNorm(B₀−C)`. Equation (9) is exactly `e_C≤e₀+R`, with coefficient one and the same tail on both sides.

The algebra is the exact matrix identity `A−C=(A−B₀)+(B₀−C)`. The independently audited frozen-norm triangle theorem applies to these two summands and proves `NuclearNorm(A−C)≤NuclearNorm(A−B₀)+NuclearNorm(B₀−C)`. Subtracting the same `τ` gives Equation (9). This implication does not need a spectral gap, `τ>0`, an eigenbasis alignment, a PSD ordering between `A` and `C`, or an extra dimension/rank factor. It remains true for ties and zeros, including empty dimensions as an algebraic fact. The public source theorem retains the Target range `1≤k<n` and both independent supplied decompositions for exact source alignment.

## Proposed exact Lean theorem

```lean
namespace NLA.Proofs.RA10

theorem matchedLeading_compression_excess_le {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat) :
    let P := selectedProjection k QAhat
    let B₀ := NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t)
      eigenvaluesA QAhat
    let C := P * A * P
    let τ := ∑ i : Fin n, if k ≤ i.val then eigenvaluesA i else 0
    let R := NLA.Statements.RA10.NuclearNorm (B₀ - C)
    let e₀ := NLA.Statements.RA10.NuclearNorm (A - B₀) - τ
    let e_C := NLA.Statements.RA10.NuclearNorm (A - C) - τ
    e_C ≤ e₀ + R := by
  ...

end NLA.Proofs.RA10
```

This is a new partial gate toward source Equation (15), not a proof of the full RA-10 Target. Direct pinned Lean 4.33.1/LeanCert kernel checking and separate imported exact-signature/source/axiom review are required before aggregate import.
