# TR-14 quotient and Frobenius pairing: independent mathematical pre-review

**Reviewer:** `/root/tr14_frob_review` (independent AI agent), 10 October 2026. **Verdict:** approved for implementation of the stated *conditional* quotient and chart lemmas. This review precedes Lean implementation of this contract and does not certify `NLA.Statements.TR14.Target`.

## Exact reviewed inputs

| Input | SHA-256 |
| --- | --- |
| Contract `QUOTIENT_FROBENIUS_PRE_REVIEW.md` | `3b8d8d1484755f149c61feb992255c6be617f659219eb0c1bf96b165c0134eea` |
| Canonical `tensor-computations/TR-14/README.md` | `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86` |
| Canonical `tensor-computations/TR-14/solution.tex` | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66c282716c14bc6` |
| Frozen `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Audited `lean-statements/NLA/Proofs/TR14/ApolarMinimal.lean` | `0e98ae3b414d2130bebe7470a25c7c8b3e422225b5581ae4b93d036f39f520d9` |

I also compared the existing `MomentIndex.lean`, `NormalizedQuotient.lean`, and approved moment algebra and apolar minimality pre-reviews. No existing compiled lemma proves the Frobenius pairing or the `GL₂` chart transport.

## Mathematical checks

- The contract preserves the frozen universal quantifiers `m≥3`, `n≥2`, every complex moment vector, and every width. Its `r₀` is the least nonzero **homogeneous apolar degree**, distinct from the arbitrary width in `Target`; a trailing zero coefficient remains allowed before chart normalization. The zero moment vector is correctly separated.
- In the chart `G(X,Y)=∑_{i=0}^{r₀}g_iX^{r₀-i}Y^i`, the coefficient `g_{r₀}` is `G(0,1)`. Since a nonzero homogeneous binary form is nonzero on some projective direction, an invertible substitution can make this coefficient nonzero and scaling makes the affine polynomial monic of degree exactly `r₀`. The **same** substitution, with inverse action on `L_D`, carries every apolar kernel: `L'_D((φ_TG)(φ_TQ))=L_D(GQ)`. The action on degree-`q` mode polynomials is invertible and, applied in all `m` modes, preserves ordinary and symmetric widths and the original-coordinate rank comparison. Merely assuming the original coefficient is nonzero would lose valid inputs.
- For a monic polynomial of degree `r₀≥1`, the exact apolar shifts are `0≤j≤D-r₀`. They propagate the quotient functional from powers `0,…,r₀−1` through **every** `h'_j` with `j≤D`, including the first new power `r₀` and endpoint `D`. At `D=2r₀−2` the shifts are `0,…,r₀−2`, as stated. The quotient dimension is exactly `r₀`.
- The radical `J={a:∀b, λ(ab)=0}` is an ideal by commutativity and associativity. If nonzero, ideal correspondence for `ℂ[t]/(g)` yields a monic proper divisor `g'|g` with `deg g'<r₀` and `[g']∈J`. Therefore `λ([t^jg'])=0` for every `j≥0`; for `j≤D-deg g'` the all-moment identity turns these into **every** degree-`deg g'` apolar equation. This contradicts minimality. If `deg g'=0`, then `g'=1`, `J=A_g`, and `λ=0`; the all-moment identity forces `h'=0`. Thus this endpoint is also excluded. The argument establishes the stated full bilinear nondegeneracy, not just `λ≠0`.
- The product of `m` degree-`≤q` mode polynomials has degree `≤mq=D`. Consequently the all-moment identity extends by linearity to the exact frozen Hankel tensor, with zero-based `Fin n` coordinates and no conjugation. The source's middle catalecticant has row degree `⌊D/2⌋` and column degree `⌈D/2⌉`; both polynomial truncations surject onto the quotient because `r₀≤⌊D/2⌋+1`. The contract correctly postpones this rank theorem and its original-coordinate transport.

## Implementation boundaries to retain

The signature sketches must make `g` a polynomial of **exact degree** `r₀` (or a `Fin(r₀+1)` coefficient vector with last coefficient one), not an unbounded polynomial with only a selected coefficient equal to one. The chart theorem should explicitly export `h'≠0` or derive it from the invertible degree-`D` action before applying the conditional Frobenius theorem. The source's `GL₂` substitution orientation must be used consistently in all homogeneous degrees and each mode, so the displayed pairing identity is proved rather than assumed.

These are elaboration and bridge obligations, not objections to the frozen mathematical assertions. A normalized quotient result alone remains conditional. The Frobenius lemma, original-coordinate middle rank, balanced apolar-space dimension, local CRT factors, symmetric upper bounds, arbitrary ordinary-decomposition lower bound, and all-width padding are still needed for `Target`. A later Lean source must receive a separate exact-signature, proof-escape, imported LeanCert kernel, and axiom audit.
