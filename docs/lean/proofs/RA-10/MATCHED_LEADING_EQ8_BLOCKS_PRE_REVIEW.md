# RA-10 Equation (8): complementary nuclear blocks and exact excess accounting

**Status:** source-locked mathematical, numerical, and indexing precontract for independent review. No Lean implementation of these proposed declarations is claimed. The permanent RA-10 ID, canonical README, frozen `NLA.Statements.RA10.Target`, and its supplied bases/quantifiers remain unchanged.

## Source and audited dependency locks

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `docs/lean/proofs/RA-10/CONSTANT_ELEVEN_TRANSFER_PRE_REVIEW.md` | `43ec3208c3177ff931289bc236f9afa32796c25be96fc07127027654f2623a92` |
| `lean-statements/NLA/Proofs/RA10/NuclearPinching.lean` | `94b0777dc73b1d23bceeda78714a5e1788d1c5ed8f677a7258401bc71b8ff033` |
| `lean-statements/NLA/Proofs/RA10/NuclearTraceDualAttains.lean` | `b8fae6f00347edbde995baae4933a752154fc0312944f17b708b7e2c3bcee991` |
| `lean-statements/NLA/Proofs/RA10/NuclearNormTriangle.lean` | `aa58d4301953e3ead89eff907d0f02f3d5e88fe7d530d06fa7de5d844e40614f` |
| `lean-statements/NLA/Proofs/RA10/MatchedLeadingSupport.lean` | `426403f51df54d1ffa70f839b18921da2a9b63ea265112213e8c66d2530c0c18` |
| `lean-statements/NLA/Proofs/RA10/CustomPSDMathlibBridge.lean` | `ca0e97485f3538275f12006d3619687d4c49bf0c1e7a8e2f698dadf87b64e0b7` |
| `lean-statements/NLA/Proofs/RA10/SelectedProjectionBasic.lean` | `cfda9a5c7a4681542e47c967d5a4011e42b28f7cb3891bd3d192a7d336bea22b` |
| `lean-statements/NLA/Proofs/RA10/SelectedProjectionIdempotent.lean` | `8ac0fb000300bca16bacdbefe1d0e8c4286418df8bc1c466081e6a1edf966a78` |

Source Section 3, Equation (8), says that pinching `A−B₀` into the selected `P` and `I−P` blocks cannot increase its nuclear norm, the complement is PSD, and consequently `e₀≥R+L`. The coefficient-one pinching theorem is now independently kernel audited. The remaining gap is exact **additivity of the nuclear norm on orthogonal blocks**, the PSD block's nuclear norm equals its trace, and the trace subtraction/tail bookkeeping below. These are independent kernel obligations, not new assumptions for the final Target.

## Exact generic matrix facts

Let `Pᵀ=P`, `P²=P`, and `Q=I−P`. For arbitrary real square matrices `X,Y` supported as `PXP=X` and `QYQ=Y`, all mixed products `XᵀY`, `YᵀX`, `XYᵀ`, `YXᵀ` vanish. The two blocks act between orthogonal domain and range subspaces. Their singular values form the multiset union of the two block singular-value multisets, **including the zero padding to dimension `n`**. Hence

```
NuclearNorm (X+Y) = NuclearNorm X + NuclearNorm Y.
```

This is exact coefficient-one additivity for the literal frozen sum over `Fin n`. It is valid for nonsymmetric `X,Y`, zero/full-rank `P`, singular blocks, and `Fin 0`. It must be kernel proved through an orthogonal direct-sum/singular-value argument or an exact trace-dual witness assembled on complementary blocks. Ordinary triangle inequality gives only the reverse inequality and does not prove this gate.

### Exact contractive trace-dual intermediate

For every `n`, real square matrices `W,M`, and the **pointwise Euclidean contraction**

```
∀ x : EuclideanSpace ℝ (Fin n), ‖Matrix.toEuclideanLin W x‖ ≤ ‖x‖,
```

prove the sharp coefficient-one statement

```
Matrix.trace (W.transpose * M) ≤ NuclearNorm M.
```

This is a private helper for complementary-block additivity, not a replacement definition of the frozen nuclear norm. Its exact derivation expands the matrix trace over an orthonormal Gram eigenbasis `bᵢ` for `M`: each pairing satisfies

```
⟪W bᵢ, M bᵢ⟫ ≤ ‖W bᵢ‖ ‖M bᵢ‖
              ≤ ‖M bᵢ‖ = singularValues(M,i),
```

where the last equality is the already kernel-audited same-index Gram/singular-value identity used in the orthogonal trace upper gate. Summing over **all** `i : Fin n` gives exactly the frozen nuclear norm, including zero singular values and `Fin 0`. No dimension or rank factor appears. The proof does not assume `W` orthogonal.

To instantiate this helper, obtain independent orthogonal trace-attaining witnesses `U_X,U_Y` for `X,Y`, put `Q=I−P`, and set `W=P U_X P+Q U_Y Q`. Symmetry and idempotence of `P`, together with `U_XᵀU_X=U_YᵀU_Y=I`, yield the exact Gram deficit identity

```
I−WᵀW = (Q U_X P)ᵀ(Q U_X P) + (P U_Y Q)ᵀ(P U_Y Q) ⪰ 0.
```

Thus `‖Wx‖≤‖x‖` for every Euclidean `x`. Support `PXP=X` and `QYQ=Y`, plus trace cyclicity, give `tr(Wᵀ(X+Y))=tr(U_XᵀX)+tr(U_YᵀY)=NuclearNorm X+NuclearNorm Y`. The contraction upper bound proves the missing `≥` direction; the audited nuclear triangle proves `≤`. The argument uses the literal original supports and does not silently require `X` or `Y` to be PSD or symmetric.

For every real `Matrix.PosSemidef Y`, prove

```
NuclearNorm Y = Matrix.trace Y.
```

One available route uses the independently audited orthogonal trace duality. Its upper bound with `U=I` gives `tr Y≤NuclearNorm Y`. For an attaining orthogonal `U`, diagonalize the actual PSD `Y` with nonnegative eigenvalues `λᵢ`. Then `tr(UᵀY)=Σᵢ λᵢ⟨Uqᵢ,qᵢ⟩≤Σᵢ λᵢ=tr Y`, since each `qᵢ` and `Uqᵢ` has norm one. Every equality, including the trace/eigenvalue equality and `Fin 0`, must be kernel proved. No replacement of the frozen nuclear norm by a trace is permitted except under the displayed PSD premise.

## Exact source Equation (8) calculation

Retain **both supplied independent bases** `QA` and `QAhat`. Put `P=selectedProjection k QAhat`, `Q=I−P`, `B₀=FunctionTruncation k id eigenvaluesA QAhat`, and `C=PAP` (the actual compression). The audited source support theorem gives `PB₀P=B₀` even though `B₀` uses values of `A` in the selected basis of `Ahat`; selected projection symmetry and idempotence come from the supplied `hAhat`. Thus

```
pinch P (A−B₀) = (C−B₀) + Q A Q.
```

The first summand is supported on `P`; the second on `Q`. The latter is PSD because `A` is PSD and `Qᵀ=Q`, so its nuclear norm is `tr(QAQ)`. The exact trace identities are

```
tr(QAQ) = tr A − tr C,
tr A = Σ_{i:Fin n} eigenvaluesA i.
```

Define zero-based source quantities, with **strict** top cutoff and complementary tail:

```
S_top = Σ_{i:Fin n} (if i.val < k then eigenvaluesA i else 0),
τ     = Σ_{i:Fin n} (if k ≤ i.val then eigenvaluesA i else 0),
R     = NuclearNorm (B₀−C),
L     = S_top − tr C,
e₀    = NuclearNorm (A−B₀) − τ.
```

Then `tr A=S_top+τ`; sign homogeneity gives `NuclearNorm(C−B₀)=R`. Pinching contraction followed by orthogonal-block additivity and PSD trace yields exactly

```
R + L ≤ e₀.
```

This is the source's Equation (8), with **no factor of two**, no dimension/rank term, no spectral gap, no positivity of `τ`, and no assumption that `QA=QAhat`. The source uses one-based `i≤k`/`i>k`; Lean's cutoffs above are `i.val<k`/`k≤i.val`. In the frozen Target range `1≤k<n`; the displayed calculation remains valid for zero/full selected subspaces and `Fin 0` as well. Keeping the public source theorem in the Target's `1≤k<n` range is sufficient, but the generic block/PSD gates must cover every `n`.

## Proposed exact Lean declarations

The generic helpers may be separate modules and audited one at a time. The source theorem may use the exact `let` variables below; elaborated matrix types and names may vary, but the mathematical hypotheses and conclusion must remain identical:

```lean
namespace NLA.Proofs.RA10

theorem nuclearNorm_complementary_blocks_add {n : ℕ}
    (P X Y : Matrix (Fin n) (Fin n) ℝ)
    (hsym : P.transpose = P) (hid : P * P = P)
    (hX : P * X * P = X)
    (hY : (1 - P) * Y * (1 - P) = Y) :
    NLA.Statements.RA10.NuclearNorm (X + Y) =
      NLA.Statements.RA10.NuclearNorm X + NLA.Statements.RA10.NuclearNorm Y := by
  ...

theorem nuclearNorm_eq_trace_of_posSemidef {n : ℕ}
    (Y : Matrix (Fin n) (Fin n) ℝ) (hY : Matrix.PosSemidef Y) :
    NLA.Statements.RA10.NuclearNorm Y = Matrix.trace Y := by
  ...

theorem matchedLeading_excess_ge_remainder_plus_loss {n k : ℕ}
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
    let S_top := ∑ i : Fin n, if i.val < k then eigenvaluesA i else 0
    let τ := ∑ i : Fin n, if k ≤ i.val then eigenvaluesA i else 0
    let R := NLA.Statements.RA10.NuclearNorm (B₀ - C)
    let L := S_top - Matrix.trace C
    let e₀ := NLA.Statements.RA10.NuclearNorm (A - B₀) - τ
    R + L ≤ e₀ := by
  ...

end NLA.Proofs.RA10
```

The private helper may be implemented with this exact Lean signature before the public block theorem:

```lean
private theorem trace_contracting_le_nuclearNorm {n : ℕ}
    (W M : Matrix (Fin n) (Fin n) ℝ)
    (hW : ∀ x : EuclideanSpace ℝ (Fin n),
      ‖Matrix.toEuclideanLin W x‖ ≤ ‖x‖) :
    Matrix.trace (W.transpose * M) ≤
      NLA.Statements.RA10.NuclearNorm M := by
  ...
```

The generic block theorem's support hypotheses are internal exact matrix equations, discharged by the actual `B₀,C,Q` in the source theorem. The PSD theorem's hypothesis is discharged by the actual `QAQ`, using `hA`, not added to `TransferBound`. The final theorem has only the two original supplied decompositions and Target-range indices as premises. Any helper module must pass direct pinned Lean 4.33.1/LeanCert kernel checks and a separate imported exact-signature/source/axiom audit before aggregate import. If complementary-block additivity cannot be proved, Equation (8) stays open; do not install it as an axiom or substitute a weaker factor.

Full source Equations (9)–(13), compression Lemma 2, arbitrary selected approximants, operator-monotone integral transfer, and the RA-10 Target remain separate obligations.
