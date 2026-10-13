# RA-10 Equation (14) with a constructed spectral decomposition of C=PAP

**Status:** source-locked mathematical, indexing and numerical precontract for independent review. No Lean implementation or nuclear ideal estimate is claimed.

## Frozen sources

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `lean-statements/NLA/Proofs/RA10/MatchedLeadingEq14Restricted.lean` | `fa51611236471f41313689afaf6853a7b9c8b3ad51aae5c775819802297c2dd9` |
| `lean-statements/NLA/Proofs/RA10/SelectedCompressionOrderedSpectral.lean` | `d4ac007b8f7dbd53c1e107bd99a76ee30dbc70f189fea28fc71f91545fab0504` |

Source Section 3 defines `P` in exactly the supplied selected `QAhat` eigenvectors, `B₀` in those same columns using the original ordered `eigenvaluesA`, and `C=PAP`. The reviewed restricted Equation (14) identity currently requires a separately supplied ordered PSD decomposition `hC` **of that actual C**. The newly kernel-proved ordered spectral bridge constructs such a decomposition from the source's existing `hA` and `hAhat` premises, including ties/zeros/empty dimension. This gate combines them without adding a new hypothesis.

## Exact mathematical and numerical scope

For arbitrary `n,k`, `s>0`, and the independent supplied ordered PSD decompositions of `A` and `Ahat`, there exist `eigenvaluesC : Fin n→ℝ` and `QC : Matrix (Fin n) (Fin n) ℝ` such that **all four frozen ordered PSD conjuncts** hold for `C=PAP`. For these same witnesses, both exact source Equation (14) matrix and frozen nuclear norm equalities hold:

```text
FunctionTruncation k (ridgeAtom s) eigenvaluesA QAhat
  − FunctionMatrix (ridgeAtom s) eigenvaluesC QC
= s • ((P*RB*P) * (B₀−C) * RC),

NuclearNorm (FunctionTruncation k (ridgeAtom s) eigenvaluesA QAhat
  − FunctionMatrix (ridgeAtom s) eigenvaluesC QC)
= NuclearNorm (s • ((P*RB*P) * (B₀−C) * RC)).
```

Here `RB=(sI+B₀)⁻¹` and `RC=(sI+C)⁻¹` exactly. These identities preserve the source's subtraction orientation, noncommutative multiplication order, the factor `s`, selected projection and **actual** C. The nuclear norm equality is only congruence of an exact matrix equality. It is not the source numerical inequality `≤ (1/(s+c)) NuclearNorm(B₀−C)`, which still needs a kernel-proved nuclear ideal property and the sharp L2 factor bounds.

The witnesses for C may be chosen by the corrected ordered spectral theorem; they do not replace or permute the original `QA`, `QAhat`, `eigenvaluesA`, or `eigenvaluesAhat`. The theorem is valid for `k=0`, `k=n`, `k>n`, and `n=0`, conditional only on the existing source decompositions and `s>0`. The target's `1≤k<n` and positive cutoff `c=a_k` are not needed for this identity gate. The prior restricted Eq14 theorem remains universal over **any** supplied `hC` of actual C; this corollary gives one constructed witness without weakening it.

## Proposed exact Lean declaration

Use a new `NLA.Proofs.RA10.MatchedLeadingEq14Constructed` module. The conjunction binds a single common pair of witnesses to the PSD, matrix and nuclear equalities.

```lean
namespace NLA.Proofs.RA10

theorem matchedLeading_ridgeProduct_constructed {n k : ℕ} {s : ℝ}
    (hs : 0 < s)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat) :
    let P := selectedProjection k QAhat
    let B₀ := NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat
    let C := P * A * P
    let RB := (s • (1 : Matrix (Fin n) (Fin n) ℝ) + B₀)⁻¹
    let RC := (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹
    ∃ (eigenvaluesC : Fin n → ℝ) (QC : Matrix (Fin n) (Fin n) ℝ),
      NLA.Statements.RA10.OrderedPSDSpectralDecomposition C eigenvaluesC QC ∧
      NLA.Statements.RA10.FunctionTruncation k (ridgeAtom s) eigenvaluesA QAhat -
        NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesC QC =
          s • ((P * RB * P) * (B₀ - C) * RC) ∧
      NLA.Statements.RA10.NuclearNorm
        (NLA.Statements.RA10.FunctionTruncation k (ridgeAtom s) eigenvaluesA QAhat -
          NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesC QC) =
        NLA.Statements.RA10.NuclearNorm
          (s • ((P * RB * P) * (B₀ - C) * RC)) := by
  ...

end NLA.Proofs.RA10
```

## Independent review boundary

Check that the existential C witnesses are the same across all three conjuncts, the C decomposition is of the **actual** `PAP`, all original supplied basis/decomposition quantifiers remain, the numerical/nuclear equality is literal and does not imply the source inequality, and every empty/tie/zero case remains. After approval, implement with pinned Lean 4.33.1/LeanCert kernel, freeze source and request imported exact-signature/source/axiom audit. Source Lemma 2, pinching, compression min-max, Equation (14)'s nuclear ideal inequality, arbitrary selected approximants and full RA-10 Target remain open.
