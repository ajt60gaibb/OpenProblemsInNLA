# RA-10 exact nonzero intersection of the supplied spectral coordinate cuts

**Status:** source-locked mathematical and indexing precontract for independent review. No Lean implementation, compression eigenvalue comparison, or full target proof is claimed.

## Frozen source and preceding gates

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `lean-statements/NLA/Proofs/RA10/SelectedCompressionEigenvalue.lean` | `00c62e352faab14482b768bd95ceadbcb76ebb6a69e69ad2d6979376aa142d13` |
| `lean-statements/NLA/Proofs/RA10/OrderedSpectralRayleigh.lean` | `3a7c03df2db70a97f16fcf05a00585e3f25d10fc523c27f2a3c31a6f9c1a4fc8` |

The RA-10 archived solution, Section 3, invokes min-max for the actual compression `C=PAP` to conclude source one-based `0≤h_i≤a_i` for `1≤i≤k`. The independently approved compression eigenvalue precontract maps this to a zero-based `a : Fin n` with `a.val<k`. Its unfinished geometric step needs one **nonzero** vector whose supplied `QC` coordinates are supported on `b≤a` and whose supplied `QA` coordinates are supported on `b≥a`. The preceding Rayleigh gate provides exact coefficient-one inequalities once these coordinate conditions hold.

## Exact finite-dimensional mathematics and indices

For arbitrary real square matrices `QC, QA : Matrix (Fin n) (Fin n) ℝ` and any `a : Fin n`, define

```text
coord_Q(x,b) = Σ_i x_i Q_i,b.
```

There are `n−1−a.val` strict-suffix conditions `coord_QC(x,b)=0` for `a.val<b.val`, and `a.val` strict-prefix conditions `coord_QA(x,b)=0` for `b.val<a.val`. Their total is exactly `n−1`, leaving a nonzero solution to these homogeneous real linear equations in `n` unknowns. This does not require orthogonality, PSD, or any relation between the matrices. Consequently it applies unchanged to the *original supplied* `QC` and `QA`, including arbitrary tie bases and zero eigenspaces, without reselection.

Equivalently, let `S_C={b : Fin n // a.val<b.val}` and `S_A={b : Fin n // b.val<a.val}`. The coordinate restriction map

```text
T : (Fin n→ℝ) →ₗ[ℝ] ((S_C→ℝ) × (S_A→ℝ))
T(x) = (b ↦ coord_QC(x,b), b ↦ coord_QA(x,b))
```

has domain dimension `n` and codomain dimension `(n−1−a.val)+a.val=n−1`; it therefore has nontrivial kernel. The selected nonzero `x` must satisfy both coordinate conditions *simultaneously*. A proof may use `LinearMap.finrank_range_add_finrank_ker`, injectivity/finite-rank monotonicity, or subspace dimension. The codomain dimension equality is the index arithmetic that needs kernel verification. For `n=1`, `a=0`, both coordinate sets are empty and any nonzero x suffices. For `n=0`, no `a : Fin 0` exists. No `k` assumption is needed for this generic geometric statement; later the approved comparison uses it only with `a.val<k≤n`, including `k=n`. Ties and zero eigenvalues have no effect on this intersection.

## Proposed exact Lean declaration

Create a new `NLA.Proofs.RA10.OrderedSpectralIntersection` module, importing the frozen Rayleigh gate. Keep both actual supplied bases explicit. This theorem is intentionally more general than its RA-10 application and has **no** hidden eigenvalue or matrix order premise.

```lean
namespace NLA.Proofs.RA10

theorem orderedSpectral_prefix_suffix_nonzero_intersection {n : ℕ}
    (QC QA : Matrix (Fin n) (Fin n) ℝ) (a : Fin n) :
    ∃ x : Fin n → ℝ,
      x ≠ 0 ∧
        (∀ b : Fin n, a.val < b.val →
          (∑ i : Fin n, x i * QC i b) = 0) ∧
        (∀ b : Fin n, b.val < a.val →
          (∑ i : Fin n, x i * QA i b) = 0) := by
  ...

end NLA.Proofs.RA10
```

The exact output is a nonzero vector and the two strict coordinate cuts; a zero vector witness would make the subsequent coefficient-one comparison invalid. The order of `QC` and `QA` matches the first C prefix/later A suffix in Section 3. Do not swap either strict direction or replace supplied matrices by a newly chosen basis.

## Application boundary and remaining obligations

For the original `hC` of **actual** `C=selectedProjection k QAhat * A * selectedProjection k QAhat` and original `hA`, instantiate this theorem with their supplied `QC, QA`. If `eigenvaluesC a>0`, every C eigenvector indexed `b≤a` is P-supported by the already proved positive-eigenvector helper and antitonicity. Completeness of the orthonormal QC basis must then show the intersection vector is P-supported. At that point `xᵀCx=xᵀAx`; the already proved prefix/suffix Rayleigh bounds and `∑x_i²>0` give `eigenvaluesC a≤eigenvaluesA a`. If `eigenvaluesC a=0`, hA nonnegativity suffices. Those support, quadratic equality, cancellation and final comparison steps are **not** claimed by this intersection gate.

Independent review should check the `n−1` constraint count, the zero-based strict cutoff and coordinate orientation, nonzero witness, empty dimension, ties/zeros, and fidelity to source one-based `h_i≤a_i`. After approval, implement only the exact theorem in pinned Lean 4.33.1/LeanCert kernel mode, freeze source SHA, and request independent imported exact-signature/source/axiom audit. Nuclear pinching, Lemma 2, Equation (14)'s nuclear ideal bound, arbitrary selected approximants, integral representation, and full RA-10 Target remain open.
