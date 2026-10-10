# SP-14: explicit finite base-Jacobian inverse

**Author:** `/root/sp14_base_proof`, 10 October 2026. **Status:** mathematical and exact-numerical pre-implementation contract; no Lean source for this gate yet. The original negative target is `lean-statements/NLA/Statements/SP14.lean`, SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`. The canonical source is `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex`, SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`, especially equation `\eqref{eq:base-preconditioner}` immediately after the displayed base triangular Jacobian (source lines 619–625). The existing Lean matrix is `NLA.Proofs.SP14.baseJetMatrix` in `BaseJetTriangular.lean`, SHA-256 `a1cff804e204a656bed6f0b45d06d0d0e0f238d385468bcda4384b72cd790ccc`. This gate refines its already proved abstract matrix-inverse solve with the source's actual coefficient formula. It is one finite algebra component of the separately approved actual-background oversampling contract, SHA-256 `5b52aaf4103ac675f74797cbd17ba63c39fdca5556b5203076c15a5cd889db68`.

## Exact finite statement and Lean-facing signatures

For `n : ℕ`, let `a_n = Ring.choose (1/2 : ℝ) n = baseCoeffReal n` and `b_n = Ring.choose (-1/2 : ℝ) n`. Define, for every `q : ℕ`, matrices over `Fin q` by

\[
 M^{(q)}_{kd} = \begin{cases}-2(k+1)a_{d-k},& k\le d,\\0,&d<k,\end{cases}
 \qquad
 N^{(q)}_{dk} = \begin{cases}-\frac{1}{2}\frac{b_{k-d}}{k+1},&d\le k,\\0,&k<d.\end{cases}
\]

The row/column orientation is fixed: `M = baseJetMatrix q` has output row `k` and correction column `d`; `N` has correction row `d` and output column `k`. The intended public Lean surface, possibly with equivalent elaborated notation, is:

```lean
noncomputable def baseInverseCoeff (n : ℕ) : ℝ :=
  Ring.choose (-1 / 2 : ℝ) n

noncomputable def baseJetInverseMatrix (q : ℕ) : Matrix (Fin q) (Fin q) ℝ :=
  fun d k => if d ≤ k then
    -(1 / 2 : ℝ) * baseInverseCoeff (k.val - d.val) / (k.val + 1 : ℝ)
  else 0

theorem baseCoeffReal_inverse_convolution (n : ℕ) :
  (∑ p ∈ Finset.antidiagonal n,
    baseCoeffReal p.1 * baseInverseCoeff p.2) =
    if n = 0 then 1 else 0

theorem baseJetMatrix_mul_inverseMatrix (q : ℕ) :
  baseJetMatrix q * baseJetInverseMatrix q = 1

theorem baseJetInverseMatrix_mul_baseJetMatrix (q : ℕ) :
  baseJetInverseMatrix q * baseJetMatrix q = 1

theorem baseJetSolve_eq_explicit (q : ℕ) (x : Fin q → ℝ) :
  baseJetSolve q x = (baseJetInverseMatrix q).mulVec x
```

The scalar inverse convolution is the coefficient of `X^n` in `(1+X)^(1/2)(1+X)^(-1/2)=1`, via Mathlib's `PowerSeries.binomialSeries_add`, with the `n=0` coefficient exactly `1`. The matrix products are **both** identities, not just an unverified right inverse. In `MN`, the `k,j` entry for `k≤j` is `(k+1)/(j+1) ∑_{r=0}^{j-k} a_r b_{j-k-r}`; the ratio becomes `1` precisely when the convolution can be nonzero (`k=j`). In `NM`, the `d,e` entry for `d≤e` is `∑_{r=0}^{e-d} b_r a_{e-d-r}` because the factors `(k+1)` cancel. Entries below the respective upper triangles vanish. Associativity, finite reindexing, and the existing nonsingularity of `M` may permit proving only one matrix product directly and deriving the other, but both public equations and the explicit solve are required.

For `q=0`, both matrices are the unique empty `Fin 0` square matrix, both products equal identity, and `baseJetSolve 0` equals the empty vector; the formula is not restricted to `q>0`. For `q=1`, `M=[-2]`, `N=[-1/2]`. For `q=2`,

\[
 M=\begin{pmatrix}-2&-1\\0&-4\end{pmatrix},\qquad
 N=\begin{pmatrix}-1/2&1/8\\0&-1/4\end{pmatrix}.
\]

For `q=3`, the explicit solve is

\[
 v_0=-x_0/2+x_1/8-x_2/16,\qquad
 v_1=-x_1/4+x_2/12,\qquad
 v_2=-x_2/6.
\]

Substitution into the displayed `M` gives `x_0,x_1,x_2` exactly; these rational checks fix the sign, denominator, and reversed degree orientation. No floating-point verification is used.

## Relation to the actual-background operator and remaining gates

The source defines `\mathcal A_g x = (\mathcal J_g ((J^0)^{-1}x))\circ f` on polynomial input. This lemma will identify its `(J^0)^{-1}` with the source's displayed finite binomial formula. It does **not** construct the actual limiting Jacobian `\mathcal J_g`, conformal map `f`, Sobolev extensions, compatible inverse operators, or their `2^100` bounds. It neither solves the nonlinear packet stage nor proves the original negative `Target`. Those obligations remain as stated in the approved actual-background oversampling contract.

The new Lean module must stay unimported until a separate source/signature/kernel audit. No axiom, `sorry`, `unsafe`, `native_decide`, or widened abstract premise is permitted.
