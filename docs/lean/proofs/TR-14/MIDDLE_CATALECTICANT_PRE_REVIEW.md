# TR-14 exact middle catalecticant rank: pre-proof contract

**Author:** `/root` (AI agent), 10 October 2026. **Status:** frozen mathematical contract for independent review before Lean implementation. This is the next part of the canonical moment-algebra lemma after the conditional quotient/Frobenius gate; it is not the all-width `TR14.Target`.

## Exact normalized-chart assertion

Fix `D≥1`, a nonzero moment vector `h : Fin (D+1) → ℂ`, and its least nonzero homogeneous apolar degree `r₀` from `ApolarMinimal.lean`. Thus `1≤r₀≤⌊D/2⌋+1`. In a chart where the chosen degree-`r₀` apolar polynomial `g` is **monic of exact degree `r₀`**, let `A=AdjoinRoot g`, `t̄=AdjoinRoot.root g`, and let `λ:A→ₗ[ℂ]ℂ` be the quotient functional. The preceding gate must prove both `λ(t̄^j)=h_j` for every `0≤j≤D` and the full Frobenius assertion `∀a, (∀b, λ(a*b)=0) → a=0`. No quotient dimension, full moment match, or Frobenius property may be inserted as a premise of the frozen global Target.

Put `a=⌊D/2⌋`, `b=⌈D/2⌉=D-a`, and define the **actual zero-based middle Hankel matrix**

\[
C_h : (a+1)\times(b+1),\qquad (C_h)_{ij}=h_{i+j}.
\]

The theorem must prove `Matrix.rank C_h = r₀` over `ℂ`. The index proof must use `i+j≤a+b=D`; no defaulted out-of-range moment value is allowed. Define the degree-`a` and degree-`b` quotient maps

\[
\rho_a(c)=\sum_{i=0}^{a}c_i\bar t^i,\qquad
\rho_b(d)=\sum_{j=0}^{b}d_j\bar t^j.
\]

Because `a,b≥r₀−1`, each map is onto `A`: its domain includes the power basis `1,t̄,…,t̄^{r₀−1}`. Prove the **entrywise factorization**, for every `c,d`,

\[
c^{\mathsf T}C_h d=\lambda(\rho_a(c)\rho_b(d)).
\]

It follows from all-moment matching for every `i+j≤D`, not merely the initial `r₀` moments. Frobenius nondegeneracy makes the pairing on `A` have rank `r₀`; pullback through two surjections keeps that rank. A matrix proof via explicit full-rank submatrices and kernel bounds is equivalent. The public result must retain all `D`, including balanced `D=2r₀−2`, `D=1,r₀=1`, and both odd/even middle splits. It must not replace `r₀` by a generic or squarefree degree.

## Original-coordinate assertion

The normalized theorem alone does not establish the source's equation `rank C_h=r₀` for an arbitrary original `h`: the chosen least apolar `G` may have a root at infinity. The independently approved `QUOTIENT_FROBENIUS_PRE_REVIEW.md` requires a `GL₂(ℂ)` chart substitution `φ_T` and the inverse dual action on the degree-`D` moment functional. The subsequent public theorem must prove, in every degree, the pairing identity `L'_D((φ_T P)(φ_T Q))=L_D(PQ)` for homogeneous `P,Q` of degrees `a,b`. Thus the original and normalized middle catalecticants are related by invertible left and right mode matrices and have **equal rank**. Combine this with the normalized result to obtain `Matrix.rank C_h = r₀` in the original coordinates for every nonzero moment vector. The zero tensor is a separate rank-zero endpoint.

No mode conjugation, positivity, distinct-root hypothesis, numerical approximation, or unproved genericity is permitted. The catalecticant rank alone does not prove either symmetric or arbitrary ordinary width equality; local CRT constructions and the product-space lower bound remain open.

## Source locks

| Input | SHA-256 |
| --- | --- |
| Canonical `tensor-computations/TR-14/README.md` | `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86` |
| Canonical `tensor-computations/TR-14/solution.tex` (§2, moment algebra) | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66c282716c14bc6` |
| Frozen `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Audited `lean-statements/NLA/Proofs/TR14/ApolarMinimal.lean` | `0e98ae3b414d2130bebe7470a25c7c8b3e422225b5581ae4b93d036f39f520d9` |
| Audited `lean-statements/NLA/Proofs/TR14/NormalizedQuotient.lean` | `3c6809e84eb522ad82c28f49245b80ef6da7da84cd201f46f4cbfb54a363a54d` |

An independent mathematical review must approve this source-locked contract before Lean implementation. A later frozen source requires a separate exact-signature, proof-escape, imported LeanCert kernel, and transitive-axiom audit.
