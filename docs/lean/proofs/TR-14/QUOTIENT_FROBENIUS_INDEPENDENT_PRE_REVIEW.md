# TR-14 quotient and Frobenius pairing: independent pre-proof review

**Reviewer:** `/root` (AI agent), 10 October 2026. **Verdict:** APPROVE frozen `QUOTIENT_FROBENIUS_PRE_REVIEW.md` as the exact mathematical and proposed Lean contract for the next §2 foundation. This is a source review, not a quotient proof or the full `TR14.Target`.

I compared the contract with the canonical `solution.tex` moment-algebra lemma and the frozen zero-based Hankel statement. It correctly starts from the **homogeneous** least apolar vector, which may have a root at infinity. Its chart route applies a `GL₂(ℂ)` substitution to both the vector and the degree-`D` moment functional by the dual inverse action; the displayed pairing identity preserves apolarity. It requires invertibility on every degree-`q` mode and a tensor identity in all `m` modes before any original-coordinate rank conclusion. A conditional monic affine quotient lemma alone is explicitly insufficient for the global target.

In a normalized chart, the leading coefficient one gives the exact recurrence for shifts `0,…,D−r₀`. The quotient functional is fixed by the first `r₀` moments and induction must match **every** moment through `D`, including `j=r₀` and `j=D`. The balanced `D=2r₀−2` and `r₀=1` endpoint obligations are explicit. The proposed Frobenius statement quantifies over every `a,b` in the quotient; the radical's proper-divisor contradiction genuinely uses all matched moments and the minimal apolar degree, including exclusion of degree-zero descent when `h'≠0`. The mode-product identity checks products through degree `D=m(n−1)`, preserving the frozen tensor's zero-based coordinates rather than only low moments.

The Lean declarations are API sketches. The eventual chart or coordinate-free proof must provide the stated transport and must not add monic-chart, genericity, squarefree, or selected-width assumptions to `NLA.Statements.TR14.Target`. The middle catalecticant, CRT, symmetric upper bound, and arbitrary ordinary lower bound remain separate obligations. Each frozen Lean source requires an independent exact-signature, imported LeanCert kernel, proof-escape, and axiom review.

| Reviewed input | SHA-256 |
| --- | --- |
| **`QUOTIENT_FROBENIUS_PRE_REVIEW.md`** | **`3b8d8d1484755f149c61feb992255c6be617f659219eb0c1bf96b165c0134eea`** |
| Canonical `README.md` | `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86` |
| Canonical `solution.tex` | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6` |
| Frozen `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Parent `MOMENT_ALGEBRA_PRE_REVIEW.md` | `2297de29286de55999709753278dcf84c1b4dd67640f4064baa98ba93165a840` |
| Reviewed `ApolarMinimal.lean` | `0e98ae3b414d2130bebe7470a25c7c8b3e422225b5581ae4b93d036f39f520d9` |

Changed contract or source bytes reopen this review.
