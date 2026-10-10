# SP-14 generic selected-block cofactor identity: pre-proof contract

**Author:** `/root/sp14_base_proof`, 10 October 2026. **Status:** source frozen but withheld from integration pending independent mathematical pre-review and then a separate final source/kernel audit. The fixed Target remains `lean-statements/NLA/Statements/SP14.lean`, SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`; the source paper is `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex`, SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`, Proposition “Odd-symbol pencil and its jets.” This contract is the generic finite cofactor step used by the independently approved constructive base-pencil contract `BASE_JET_RIGHT_INVERSE_PRE_REVIEW.md`, SHA-256 `bbcb1bfe929f05bfdfe1a34e5e34b8d021b2aff365c8c60e7ec4900a16f1ee4d`.

## Exact statement and orientations

For every `m : ℕ`, let `L=m+1`, take an **arbitrary** complex square matrix `G : Matrix (Fin L) (Fin L) ℂ`, and define

\[
B_{ij}=G_{i,j+1}\quad(0\le i<L,\ 0\le j<m),\qquad
C_{ij}=G_{i,j}\quad(0\le i<m,\ 0\le j<L).
\]

Thus `B=G.submatrix id Fin.succ` has shape `L×m` and `C=G.submatrix Fin.castSucc id` has shape `m×L`; the selected product is **`C*B`**, of shape `m×m`. The upper unit shift `U=baseUpperShift m` has shape `L×L` and entry `Uᵢⱼ=1` precisely when `j=i+1`. For `t:ℂ` put `H(t)=G²−(t+1)U`. Prove the following single generic Lean theorem with no triangularity or invertibility assumption:

```lean
theorem selected_charpoly_eq_pencil_adjugate (m : ℕ)
    (G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (t : ℂ) :
    ((G.submatrix Fin.castSucc id * G.submatrix id Fin.succ).charpoly).eval (t + 1) =
      (G * G - (t + 1) • baseUpperShift m).adjugate 0 (Fin.last m)
```

The **actual original Toeplitz section** is not yet part of this generic statement. The approved base-pencil contract requires a later theorem identifying the `G` built from the frozen actual Fourier coefficients with this selected product; this cofactor identity alone does not claim the base jet formula, vector existence, or the final negative Target.

## Determinant proof and endpoint

Delete the last row and first column of `H(t)`. The resulting `m×m` minor uses rows `0,…,m−1` and columns `1,…,m`; entrywise it is exactly

\[
H(t)[0{:}m-1,1{:}m]=(C B)-(t+1)I_m.
\]

Mathlib's `Matrix.adjugate_fin_succ_eq_det_submatrix` at row index `0`, column index `Fin.last m` gives

\[
\operatorname{adj}(H(t))_{0,m}=(-1)^m\det(CB-(t+1)I_m).
\]

Since `det(-A)=(-1)^m det(A)` for an `m×m` matrix, the two signs cancel and this equals `det((t+1)I_m-CB)`. By `Matrix.eval_charpoly`, that determinant is exactly `charpoly(CB).eval(t+1)`. The `Fin.castSucc` and `Fin.succ` orientation is essential: swapping them would select a different minor and sign.

At `m=0`, `B` is `1×0`, `C` is `0×1`, the characteristic polynomial of the empty `C*B` matrix is `1`, `U` is the `1×1` zero matrix, and the adjugate of any `1×1` matrix is `1`; the theorem therefore reads `1=1` even if `G` is singular. At `m=1`, both sides are `t+1-(G²)₀₁=t+1-(G₀₀G₀₁+G₀₁G₁₁)`. These endpoints should be checked by the reviewer but the Lean theorem must cover all `m` uniformly.

## Source lock and trust scope

The already written, **unimported** candidate source is `lean-statements/NLA/Proofs/SP14/BaseJetCorner.lean`, SHA-256 `4e9d3861ed43fe36db4065dc91370635a1a26c1faa99a52a8b84b5511c659f6c`. It was written before this separate review gate was identified; it remains frozen while this contract is reviewed. Direct source compilation, module build, and separate imported LeanCert audit passed with only `propext`, `Classical.choice`, `Quot.sound`, but those checks do not substitute for independent mathematical review. If the reviewer rejects this contract, the source must be revised under a newly frozen contract and reaudited. No use of `sorry`, `axiom`, `unsafe`, or a surrogate Toeplitz definition is permitted.
