# RA-10 Lemma 2: ridge compression positive-part bound

**Status:** source-only mathematical, numerical, and indexing precontract for independent review. This is the substantive missing positive-part inequality used in source Eq. (13). It is not a Lean proof or a claim about the frozen `Target`; no implementation may begin before independent approval.

## Frozen source and dependency locks

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `lean-statements/NLA/Proofs/RA10/SelectedProjectionBasic.lean` | `cfda9a5c7a4681542e47c967d5a4011e42b28f7cb3891bd3d192a7d336bea22b` |
| `lean-statements/NLA/Proofs/RA10/SelectedCompressionPSD.lean` | `ad69432066d88ff06bbdc68c1841498c4355eb5569cbb5c976745b98f90b9222` |
| `lean-statements/NLA/Proofs/RA10/HermitianPositivePart.lean` | `db272c38e076cd0e41a278d9a488f5aba5cab71f1104f146236f591a8ef3f6e8` |
| `lean-statements/NLA/Proofs/RA10/MatchedLeadingEq11Variational.lean` | `8aafb09c891e55d8de642cf5da0fd6c854ba3f9e2b50ecc4f5628ee790f46989` |
| `lean-statements/NLA/Proofs/RA10/MatchedLeadingEq12RidgeLoss.lean` | `da281781388a4c414491c18cd80c2f113c75bced4d6e82abd0a6e33b2c47037e` |
| `lean-statements/NLA/Proofs/RA10/MatchedLeadingEq13TraceIdentity.lean` | `0b3628c7cc4e9d8fc520b582748bff3643e6fe8748c07871cc559f86f6cb097b` |

The published RA-10 ID and canonical README are permanent. The frozen `NLA.Statements.RA10.Target` still quantifies over all admissible functions, both independently supplied ordered bases, all ties/zeros, and the full error premise. This document concerns one ridge-atom dependency on the positive-cutoff branch only.

## Exact source Lemma 2

For a real PSD matrix `A`, an orthogonal projector `P=Pᵀ=P²` of rank `k`, actual compression `C=P*A*P`, and arbitrary real `s>0`, `c>0`, put `D=C−A`, `f_s(x)=x/(s+x)`, and `g=1/(s+c)`. Let `H` be the restriction of `C` to `range(P)` and `d=tr((c I_k−H)₊)`. The original source Lemma 2 claims, with coefficient **two**,

```text
tr((f_s(C)−f_s(A))₊)
  ≤ 2/(s+c) * [tr((C−A)₊) + d].
```

This is valid when `H` is singular as well as positive definite; no gap, commutation, eigenbasis match, or Loewner assertion `C≤A` is assumed. The full-space matrix `c • P−C` is zero on `range(P)⊥` and restricts to `c I_k−H` on `range(P)`. Consequently the exact full-space trace `tr(hermitianPositivePart(c • P−C))` equals `d`; this support/positive-part identification must be proved in Lean or derived from an exact spectral trace theorem, not asserted by renaming. It remains true if `rank(C)<k`, since the extra selected directions contribute `max(c,0)=c`, whereas the unselected complement contributes zero.

The sign and multiplication orientation are fixed: the left side is `f_s(C)−f_s(A)`, the first right positive part is `C−A`, and the deficit matrix is `c • P−C`. Reversing either difference would be a different and generally unsupported claim. The frozen nuclear norm does **not** appear in Lemma 2; it enters Eq. (13) through the separately audited positive-part trace identity.

## Exact RA-10 source instance and indexing

For the application, retain `1≤k<n`, `(eigenvaluesA,QA)` and independent `(eigenvaluesAhat,QAhat)`, with `P=selectedProjection k QAhat` and **actual** `C=P*A*P`. Take any ordered PSD spectral witness `(eigenvaluesC,QC)` of this same `C`. Define `F_A=FunctionMatrix (ridgeAtom s) eigenvaluesA QA` and `F_C=FunctionMatrix (ridgeAtom s) eigenvaluesC QC`; these are the exact matrix functions `f_s(A)` and `f_s(C)`, including `f_s(0)=0`. The source positive-tail branch sets `c=a_k` one-based, i.e. the zero-based `eigenvaluesA ⟨k−1,_⟩`, with `c>0`. No value of `eigenvaluesAhat` is substituted for `c`.

The source-instance inequality to implement is exactly

```text
tr(hermitianPositivePart(F_C−F_A))
  ≤ 2/(s+c) *
      [tr(hermitianPositivePart(C−A))
       + tr(hermitianPositivePart(c • P−C))].
```

This preserves every matrix, basis, cutoff, orientation, and numerical constant in Lemma 2. The mathematical lemma is generic for any orthogonal `P`; the proposed Lean public theorem packages only the actual selected-projector instance needed for Eq. (13). A private generic projector proof is permitted, but a new public generic theorem requires its own exact signature and independent pre-review. The theorem may not assume `H` invertible, add a gap, replace nuclear/positive-part trace by Frobenius terms, or enlarge the factor `2/(s+c)`.

## Proof obligations before the theorem can be trusted

The source proof first handles `H≻0`. In `range(P) ⊕ ker(P)`, write `A=[[H,E],[Eᵀ,F]]` and `C=[[H,0],[0,0]]`. PSD of `A` yields `F≽EᵀH⁻¹E`. For each unit positive eigenvector of `Z=F_C−F_A` with eigenvalue `λ>0`, source Eqs. (2)–(7) use `μ=λ/(1+λ)` and prove the exact single-vector bound

```text
vᵀ(C−A)v ≥ λ(s+c)/2 − μ(2−μ) uᵀ(c I_k−H)₊u.
```

Summing over the positive eigenspace, coefficient-one trace variational bounds give `tr(Q(C−A))≤tr((C−A)₊)` and `Σ u uᵀ≼I_k`, producing `(s+c)/2 * tr(Z₊)≤tr((C−A)₊)+d`. The extension to singular `H` uses `A_r=A+rP`, `C_r=C+rP=P A_r P` for `r>0`; `C_r−A_r=C−A` exactly. Matrix ridge functions and positive-part traces converge as `r↓0`, and the selected deficit trace tends to `d`. This step must retain the same `P`, `s`, and `c`; it cannot silently assume positive definiteness of the original compression. Any alternative proof is acceptable only if it proves the same exact public statement in kernel mode.

## Proposed sole public Lean signature

After independent pre-review, the new `NLA.Proofs.RA10.RidgeCompressionPositivePart` module may expose exactly:

```lean
namespace NLA.Proofs.RA10

theorem matchedLeading_ridge_compression_positivePart_le {n k : ℕ}
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
    let P := selectedProjection k QAhat
    let C := P * A * P
    let F_A := NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesA QA
    let F_C := NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesC QC
    Matrix.trace (hermitianPositivePart (F_C - F_A)) ≤
      (2 / (s + c)) *
        (Matrix.trace (hermitianPositivePart (C - A)) +
         Matrix.trace (hermitianPositivePart (c • P - C))) := by
  ...

end NLA.Proofs.RA10
```

The proposed statement has only the source positive-cutoff hypothesis `c>0` in addition to the frozen target's matrix/basis/range data and `s>0`. It retains the arbitrary supplied ordered witness of actual `C`; ties and zeros remain allowed. The full target's `c=0` branch stays open separately. Before importing this theorem, require a direct pinned LeanCert kernel proof, frozen source hash, banned-token scan, and separate imported exact-signature/source/axiom audit. No axiom, `sorry`, native decision procedure, or weakened numerical constant is allowed.
