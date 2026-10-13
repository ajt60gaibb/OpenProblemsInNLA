# RA-10 selected spectral projector and supported functional calculus

**Status:** source-locked mathematical and exact-signature precontract for independent review. No Lean implementation or proof is claimed.

## Source lock and role

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `docs/lean/proofs/RA-10/CONSTANT_ELEVEN_TRANSFER_PRE_REVIEW.md` | `43ec3208c3177ff931289bc236f9afa32796c25be96fc07127027654f2623a92` |
| `docs/lean/proofs/RA-10/NUCLEAR_PINCHING_REFLECTION_PRE_REVIEW.md` | `81a3da38ff88411c53b211b5c5231054a9a63aefb1193b43d4953cfeb9e61669` |

The canonical solution defines `P` as the projection onto the **actual first `k` columns of the supplied `QAhat`** and retains it when selected eigenvalues vanish. This gate constructs that exact `P`, proves its projection/rank properties, and ties its supported functional calculus to the frozen entrywise `FunctionTruncation`. It does not prove the nuclear-norm pinching contraction, matrix ridge lemma, positive-integral representation, or `TransferBound 11`.

## Exact mathematics and indexing

For every `n,k : ℕ` and real square `Q`, define

```text
Pᵢⱼ = ∑_{a : Fin n, a.val<k} Qᵢₐ Qⱼₐ.
```

The selector is the **strict** zero-based condition `a.val<k`, exactly the frozen `FunctionTruncation` selector. If `Q` has orthonormal columns, its frozen equation is

```text
∑_{i : Fin n} Qᵢₐ Qᵢᵦ = if a=b then 1 else 0.
```

This is `QᵀQ=I`; because `Q` is square, also `QQᵀ=I`. With `Dₐₐ=1` for `a.val<k` and `0` otherwise, `P=QDQᵀ`. Hence `Pᵀ=P`, `P²=P`, and `rank(P)=min(k,n)`; in the frozen range `1≤k<n`, its rank is exactly `k`. The equality and projection identities hold for `k=0`, `k=n`, `k>n`, and `n=0` internally. No eigenvalue sign, gap, nonzero selected eigenvalue, or special choice among tied eigenvectors is used. Every supplied `Q` satisfying the frozen decomposition is retained unchanged.

For **every** `eigenvalues : Fin n→ℝ` and **every** `f : ℝ→ℝ` (without assuming `f(0)=0`), prove the exact frozen entrywise equalities

```text
P = FunctionTruncation k (fun _ => 1) eigenvalues Q,
P · FunctionMatrix f eigenvalues Q · P
  = FunctionTruncation k f eigenvalues Q.
```

The second identity is supported functional calculus on the selected range. For `f(0)>0`, it must not be replaced by the full functional calculus of the rank-`k` matrix `FunctionTruncation k id eigenvalues Q`, because that full calculus contributes `f(0)` on the complement. The identity includes selected zero eigenvalues and ties. In the final transfer theorem, instantiate `Q=QAhat` **once** for both the identity-function and `f` truncations; do not change the supplied basis.

## Proposed exact Lean declarations

Use a separate `NLA.Proofs.RA10.SelectedProjection` module. Stage implementation if needed, but independently review/freeze each implemented exact theorem:

```lean
namespace NLA.Proofs.RA10

def selectedProjection {n : ℕ} (k : ℕ)
    (Q : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ∑ a : Fin n,
    if a.val < k then Q i a * Q j a else 0

theorem selectedProjection_eq_functionTruncation {n : ℕ}
    (k : ℕ) (eigenvalues : Fin n → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) :
    selectedProjection k Q =
      NLA.Statements.RA10.FunctionTruncation k (fun _ => (1 : ℝ)) eigenvalues Q := by
  ...

theorem selectedProjection_transpose {n : ℕ}
    (k : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) :
    (selectedProjection k Q).transpose = selectedProjection k Q := by
  ...

theorem selectedProjection_idempotent {n k : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {eigenvalues : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (h : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvalues Q) :
    selectedProjection k Q * selectedProjection k Q = selectedProjection k Q := by
  ...

theorem selectedProjection_rank {n k : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {eigenvalues : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (h : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvalues Q)
    (hk : k ≤ n) :
    (selectedProjection k Q).rank = k := by
  ...

theorem selectedProjection_functionMatrix {n k : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {eigenvalues : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (h : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvalues Q)
    (f : ℝ → ℝ) :
    selectedProjection k Q * NLA.Statements.RA10.FunctionMatrix f eigenvalues Q *
      selectedProjection k Q =
        NLA.Statements.RA10.FunctionTruncation k f eigenvalues Q := by
  ...

end NLA.Proofs.RA10
```

The rank conclusion uses Mathlib's actual `Matrix.rank : ℕ`; the theorem requires `k≤n` solely because an `n×n` matrix cannot have rank `k>n`. The frozen final target already gives `k<n`, so this adds no new final condition. The two matrix equalities keep the exact `FunctionMatrix`/`FunctionTruncation` definitions and their original `f` argument, including arbitrary negative inputs that are never sampled by nonnegative eigenvalues in the final theorem.

## Proof obligations and review

Independently check the strict cutoff, `QᵀQ=I` to `QQᵀ=I` step, `P=QDQᵀ`, rank count including `n=0`, and supported-versus-full calculus distinction before implementing. The whole proof must be finite algebra and exact rank reasoning, no numerical sampling. Direct pinned Lean 4.33.1/LeanCert kernel checks, frozen-source exact-signature/axiom review, and aggregate import apply to each staged module. The nuclear pinching contraction remains open until a genuine proof for the frozen singular-value sum is supplied.
