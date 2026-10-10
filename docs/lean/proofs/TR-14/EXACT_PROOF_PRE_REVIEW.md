# TR-14 full-target proof: mathematical and Lean pre-review contract

**Author:** `/root` (AI agent), 10 October 2026. **Status:** draft for independent review before any TR-14 proof implementation. This contract describes a route to the unchanged `NLA.Statements.TR14.Target`; it is not a proof.

## Frozen theorem and exact scope

The final exported declaration must have the type

```lean
theorem target : NLA.Statements.TR14.Target
```

After unfolding the frozen target, this says: for **every** `m n : ℕ` with `3 ≤ m` and `2 ≤ n`, every complex moment vector `h : Fin (m * (n - 1) + 1) → ℂ`, and **every** `r : ℕ`,

```lean
OrdinaryWidth (Hankel h) r ↔ SymmetricWidth (Hankel h) r
```

Both widths are the existing exact coordinate equations in `NLA.Statements.TR14`. The index `HankelIndex i` sums the zero-based `Fin n` values, matching the canonical one-based sum minus `m`. The theorem includes `r=0`, the zero tensor, all exceptional Hankel tensors, and all nonzero ordinary factors. There is no genericity, Vandermonde, nonzero, border-rank, or bounded-dimension premise. A theorem proved only for a selected rank, for some `r`, or for rank-one symmetric factors is insufficient.

The reverse implication from a symmetric width to an ordinary width follows by absorbing the scalar into one mode; it must be proved within the exact width definitions and includes `r=0`. The substantive forward implication requires a uniform ordinary-rank lower bound and a matching symmetric construction for every nonzero tensor, then zero padding to pass from minimum rank to every `r`.

## Source proof route and endpoints

The canonical `solution.tex`, Theorem 1.1 and §§2–5, gives a stronger exact-rank formula for nonzero tensors. Put `D=m(n-1)`. Let `r₀` be the least degree of a nonzero homogeneous binary apolar polynomial, equivalently the middle Hankel catalecticant rank; choose such a degree-`r₀` polynomial and let `s` be its number of distinct projective roots. The source claims

```text
ordinary rank = symmetric rank
  = min(D - r₀ + 2, (m - 1) * r₀ - (m - 2) * s).
```

Do not confuse the invariant `r₀` with the target's arbitrary width `r`. The formula is asserted only for nonzero tensors. When the minimal apolar polynomial is not unique, the source proves `D=2*r₀-2`, so the minimum equals `r₀` independently of the polynomial choice. The zero tensor has both widths at `r=0`; padding covers larger widths. The inclusive bounds `m≥3`, `n≥2` must remain intact; `m=3`, `n=2`, squarefree and repeated-root cases, and balanced degree are part of the target. There are no floating-point or numerical certificates.

The finite moment algebra in §2 is `A=ℂ[t]/(g)`, with a Frobenius functional matching all moments through degree `D`. Its nondegenerate pairing establishes the middle catalecticant rank and permits the local factor decomposition. The two symmetric upper bounds in §3 are: local interpolation using exactly `(m-1)(ℓ_a-1)+1` root-of-unity nodes for a local root of multiplicity `ℓ_a`, totaling `(m-1)r₀-(m-2)s`; and a degree-`D-r₀+2` squarefree apolar polynomial giving a Vandermonde decomposition. Both must produce decompositions under the frozen `SymmetricWidth` semantics, including any zero weights and infinity chart changes.

The ordinary lower bound in §§4–5 is the hard step. It starts with an **arbitrary minimum-length ordinary decomposition** whose mode factors may depend on both the summand and mode. Its graph subspaces lie in `B=A×ℂ^R` and satisfy an annihilating Frobenius functional. The contextual product-space inequality applies under surjectivity of products of all but one mode onto `A`; it forces auxiliary stabilizers to be reduced and handles mixed repeated-root factors through a partition of whole local factors. For a block with algebra dimension `r_j`, `s_j` support components, and `R_j` ordinary summands, the proof obtains

```text
R_j ≥ m * min(n, r_j) - r_j - m + 2.
```

If any `r_j≥n`, this yields `R≥D-r₀+2`; otherwise summing blocks gives `R≥(m-1)r₀-(m-2)s`. A lower bound restricted to symmetric or Vandermonde decompositions would miss the original target. A generic product-space inequality in an arbitrary nonreduced algebra may not be substituted for the contextual lemma without proof of its hypotheses.

## Lean implementation and review gates

Before proof coding, independent review must check the frozen theorem signature, zero/padding reduction, the exact two upper-bound counts, and the arbitrary ordinary-decomposition lower bound against the cited source. Intermediate declarations may introduce algebraic invariants or chart choices only as proved existence, with no assumptions added to `Target`. New proof modules must remain separate from the frozen `NLA.Statements.TR14` file. Each compiled module requires a source-locked independent mathematical/signature review, imported LeanCert kernel audit, and transitive axiom report. Standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound` are acceptable; custom target axioms, `sorry`, and `native_decide` are not.

## Source locks

| Source | SHA-256 |
| --- | --- |
| `tensor-computations/TR-14/README.md` | `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86` |
| `tensor-computations/TR-14/solution.tex` | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66c282716c14bc6` |
| `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |

Changed source bytes reopen the comparison. This pre-review does not upgrade TR-14 from statement-only to a Lean proof.
