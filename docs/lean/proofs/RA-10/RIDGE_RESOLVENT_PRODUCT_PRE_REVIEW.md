# RA-10 exact noncommutative ridge resolvent product

**Status:** source-locked mathematical and exact-signature precontract for independent review. No Lean implementation or proof is claimed.

## Sources and scope

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `docs/lean/proofs/RA-10/RIDGE_RESOLVENT_MATRIX_PRE_REVIEW.md` | `55240833a50a8403c827e0da38610a81ab6b6102117999587ff8747c0c6158d2` |
| `lean-statements/NLA/Proofs/RA10/RidgeShiftInverse.lean` | `db487f99898c55bd9958b19b2cfdd576342a36fdb21ec7f6269954309bac77e0` |
| `lean-statements/NLA/Proofs/RA10/RidgeResolventMatrix.lean` | `1523abd991863c75f890cac0abfcc905948716a0179e05985f16fdf6fed233c8` |

The approved matrix bridge already proves `fₛ(C)−fₛ(A)=s(R_A−R_C)` for actual frozen `FunctionMatrix` values, where `R_X=(sI+X)⁻¹`. The source's Lemma 2 and Equation (14) additionally use a product resolvent identity. This gate supplies it with **both valid noncommutative multiplication orders**; it does not prove Lemma 2's positive-part estimate, nuclear ideal inequality, or the final transfer target.

## Exact mathematics

For every `n : ℕ`, `s>0`, and every frozen ordered PSD spectral decomposition `A,eigenvaluesA,QA`, prove `sI+A` is a unit in the square-matrix ring. The statement remains true for singular `A`, tied/zero eigenvalues and `n=0`, since each spectral scalar `s+aᵢ` is strictly positive. The earlier `spectralShift_inverse` source proved a right-inverse identity internally; this gate must expose a kernel proof of invertibility rather than infer it merely from the existence of Mathlib's total matrix inverse, which also exists syntactically for singular matrices.

For two independently supplied PSD decompositions of `A,C`, put `R_A=(sI+A)⁻¹` and `R_C=(sI+C)⁻¹`. Prove exactly

```text
fₛ(C)−fₛ(A)
  = s • (R_A · (C−A) · R_C)
  = s • (R_C · (C−A) · R_A).
```

The two products are equal because both equal `R_A−R_C`; this does **not** say `R_A` and `R_C` commute. The first follows from `R_A−R_C=R_A[(sI+C)−(sI+A)]R_C`; the second from `R_A−R_C=R_C[(sI+C)−(sI+A)]R_A`. The shift cancels exactly to `C−A`. Both retain the literal factor `s`, all matrix multiplication order, and no gap/strict-PSD/commuting condition. In source Equation (14), instantiate `A=C_source`, `C=B₀_source`; the **second** order becomes `s(sI+B₀)⁻¹(B₀−C)(sI+C)⁻¹` as printed. For the source Lemma 2, either order may be used with its block equations, but its chosen orientation must be audited.

## Proposed exact Lean declarations

Use a separate `NLA.Proofs.RA10.RidgeResolventProduct` module, importing the frozen target and reviewed ridge modules:

```lean
namespace NLA.Proofs.RA10

theorem spectralShift_isUnit {n : ℕ} {s : ℝ}
    (hs : 0 < s)
    {A : Matrix (Fin n) (Fin n) ℝ} {eigenvalues : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (h : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvalues Q) :
    IsUnit (s • (1 : Matrix (Fin n) (Fin n) ℝ) + A) := by
  ...

theorem ridgeFunctionMatrix_sub_product_left {n : ℕ} {s : ℝ}
    (hs : 0 < s)
    {A C : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesC : Fin n → ℝ}
    {QA QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition C eigenvaluesC QC) :
    NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesC QC -
      NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesA QA =
      s • ((s • (1 : Matrix (Fin n) (Fin n) ℝ) + A)⁻¹ * (C - A) *
        (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹) := by
  ...

theorem ridgeFunctionMatrix_sub_product_right {n : ℕ} {s : ℝ}
    (hs : 0 < s)
    {A C : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesC : Fin n → ℝ}
    {QA QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition C eigenvaluesC QC) :
    NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesC QC -
      NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesA QA =
      s • ((s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹ * (C - A) *
        (s • (1 : Matrix (Fin n) (Fin n) ℝ) + A)⁻¹) := by
  ...

end NLA.Proofs.RA10
```

No matrix norm appears in this gate. The exact frozen `FunctionMatrix` and ridge atom are kept; no basis-independent replacement is silently substituted. Any use of `Matrix.inv_sub_inv` must discharge its `IsUnit` premises by the proved `spectralShift_isUnit` theorem.

## Review and verification

Independent pre-review must check both product orders by multiplication, the source's Equation (14) orientation, all signs and scalar factors, shifted invertibility even for zero eigenvalues, and the `n=0` case. Implement only after approval. Direct pinned Lean 4.33.1/LeanCert kernel checks, frozen-source imported exact-signature/axiom review, and aggregate import apply to each staged module. The nuclear pinching, positive-part ridge compression, general operator-monotone representation and frozen RA-10 Target remain open.
