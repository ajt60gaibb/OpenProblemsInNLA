# RA-10 source Equation (10): positive-part trace identity for compression excess

**Status:** source-locked mathematical, numerical, and indexing precontract for independent review. The permanent RA-10 ID, canonical README, frozen `NLA.Statements.RA10.Target`, both independent supplied bases, and the original numerical coefficients remain unchanged. No proposed Eq. (10) Lean declaration has been implemented.

## Source and kernel-audited dependency locks

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `lean-statements/NLA/Proofs/RA10/NuclearComplementaryBlocks.lean` | `3345147f13e3552cb9a38f196dee457f169c333bec98fe834592c5135d74341a` |
| `lean-statements/NLA/Proofs/RA10/NuclearNormPSDTrace.lean` | `176e53e8f0f7b212631ec37ea00bd7d945f047beed2e77b0ce2eb9bc9771fa67` |
| `lean-statements/NLA/Proofs/RA10/NuclearTraceDualUpper.lean` | `67927e3c16d9244992cd37c3adeb4aa61948499688a88e6fb78df0b6c113d1e2` |
| `lean-statements/NLA/Proofs/RA10/NuclearTraceDualAttains.lean` | `b8fae6f00347edbde995baae4933a752154fc0312944f17b708b7e2c3bcee991` |
| `lean-statements/NLA/Proofs/RA10/MatchedLeadingSupport.lean` | `426403f51df54d1ffa70f839b18921da2a9b63ea265112213e8c66d2530c0c18` |
| `lean-statements/NLA/Proofs/RA10/SelectedProjectionBasic.lean` | `cfda9a5c7a4681542e47c967d5a4011e42b28f7cb3891bd3d192a7d336bea22b` |
| `lean-statements/NLA/Proofs/RA10/SelectedProjectionIdempotent.lean` | `8ac0fb000300bca16bacdbefe1d0e8c4286418df8bc1c466081e6a1edf966a78` |
| `lean-statements/NLA/Proofs/RA10/SpectralQuadratic.lean` | `23e82984e32c8724fda21446037db91ca0180f52d41602dde086d16a1f954eae` |

The pinned Mathlib real Hermitian spectral theorem (`Matrix.IsHermitian.eigenvectorUnitary`, `Matrix.IsHermitian.eigenvalues`, `Matrix.IsHermitian.spectral_theorem`) is used at its actual matrix dimension `Fin n`. Its eigenvalue index `i : Fin n` is summed without ordering assumptions; permutations, ties, zeros, and `Fin 0` leave this sum unchanged. The positive part cannot be defined through the frozen `OrderedPSDSpectralDecomposition`, which requires nonnegative eigenvalues and therefore does not apply to the generally indefinite `C−A`.

## The actual Hermitian positive part and its trace

For a real Hermitian matrix `M`, take its pinned spectral decomposition `M=U diag(λᵢ) Uᵀ` and define the **matrix** positive part

```
M₊ = U diag(max(λᵢ,0)) Uᵀ.
```

Its trace is exactly `Σ_i max(λᵢ,0)` because `UᵀU=I`. It is PSD and, together with `M₋=U diag(max(−λᵢ,0)) Uᵀ`, satisfies `M=M₊−M₋` and `M₊M₋=0`. Thus this is the source's actual spectral positive part, not an entrywise matrix maximum. A total Lean definition may return zero on non-Hermitian inputs; every use in this contract is under an independently proved `M.IsHermitian` hypothesis, so the non-Hermitian branch is irrelevant and cannot weaken the source theorem.

The exact generic trace identity to prove first is

```
NuclearNorm M = 2 * Matrix.trace (hermitianPositivePart M) − Matrix.trace M
```

for **all real Hermitian** `M` and all finite `n`. The coefficient `2` follows from the scalar identity `|λ|=2 max(λ,0)−λ`. One kernel route uses the two PSD spectral parts, the audited coefficient-one nuclear norm additivity on complementary orthogonal supports, and audited `NuclearNorm Y=tr Y` for PSD `Y`; alternatively, a spectral sign orthogonal witness and the audited trace-dual upper/attainment facts give the same equality. The generic lemma must establish the exact frozen all-`Fin n` singular-value norm; it may not replace it by an informal eigenvalue sum or a new norm. No spectral gap, invertibility, or nonzero eigenvalue premise is allowed.

## Exact source Equation (10)

Retain supplied independent `OrderedPSDSpectralDecomposition` witnesses `hA` for `A,eigenvaluesA,QA` and `hAhat` for `Ahat,eigenvaluesAhat,QAhat`; do not identify `QA` with `QAhat`. Let `P=selectedProjection k QAhat` and **actual** `C=PAP`. The supplied `hA` yields real symmetric/PSD `A`, and the audited symmetry of `P` yields real symmetric `C` and `M=C−A`; this Hermitian premise is proved internally from the original supplied witnesses. Define strict zero-based source top and tail:

```
S_top = Σ_{i:Fin n} (if i.val < k then eigenvaluesA i else 0),
τ     = Σ_{i:Fin n} (if k ≤ i.val then eigenvaluesA i else 0),
L     = S_top − tr C,
e_C   = NuclearNorm(A−C) − τ.
```

The original one-based `i≤k`/`i>k` is exactly `i.val<k`/`k≤i.val`. The audited spectral reconstruction gives `tr A=S_top+τ`. Sign invariance of the frozen nuclear norm gives `NuclearNorm(A−C)=NuclearNorm(C−A)`. Apply the generic identity to `M=C−A`, and use `tr(C−A)=tr C−tr A`, to obtain precisely

```
e_C = L + 2 * tr((C−A)₊).
```

This is source Equation (10), with coefficient **two**, no lost tail, and no factor depending on `n` or `k`. Although source Section 3 begins under `τ>0`, this algebra remains true for `τ=0`; the public source theorem retains `1≤k<n` as in the frozen Target. It covers ties, zero eigenvalues, rank-deficient compression, and all supplied selected eigenvectors.

## Proposed staged Lean declarations

The first definition and theorem may be placed in a separate generic module and audited before the source Eq. (10) theorem. The `if` branch is only a totalization; the proof of the generic identity must unfold the Hermitian branch under `hM` and identify it with the stated spectral positive part.

```lean
namespace NLA.Proofs.RA10

noncomputable def hermitianPositivePart {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  if hM : M.IsHermitian then
    let U : Matrix (Fin n) (Fin n) ℝ := hM.eigenvectorUnitary
    U * Matrix.diagonal (fun i : Fin n => max (hM.eigenvalues i) 0) * U.transpose
  else 0

theorem nuclearNorm_eq_two_trace_positivePart_sub_trace {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) :
    NLA.Statements.RA10.NuclearNorm M =
      2 * Matrix.trace (hermitianPositivePart M) - Matrix.trace M := by
  ...

theorem matchedLeading_compression_excess_positivePart {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat) :
    let P := selectedProjection k QAhat
    let C := P * A * P
    let S_top := ∑ i : Fin n, if i.val < k then eigenvaluesA i else 0
    let τ := ∑ i : Fin n, if k ≤ i.val then eigenvaluesA i else 0
    let L := S_top - Matrix.trace C
    let e_C := NLA.Statements.RA10.NuclearNorm (A - C) - τ
    e_C = L + 2 * Matrix.trace (hermitianPositivePart (C - A)) := by
  ...

end NLA.Proofs.RA10
```

The generic identity and source theorem are separate kernel obligations. Any needed intermediate spectral-sign/projection lemma must preserve the real `Fin n` dimension, exact `max` cutoff, and coefficient one in the nuclear norm before implementation. The full source Lemma 2, Equations (11)–(17), operator-monotone integral transfer, and frozen RA-10 Target remain open.
