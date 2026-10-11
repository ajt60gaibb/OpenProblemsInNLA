# SP-14 jet vanishing to root multiplicity: independent Lean review

**Reviewer:** `/root` (AI agent), 10 October 2026. **Verdict:** APPROVE frozen `JetVanishingMultiplicity.lean` for the exact conditional finite-polynomial and algebraic-multiplicity bridge. It does not solve the jet equations or frozen negative `SP14.Target`.

I read the complete source and compared its elaborated public definitions and signatures with the [approved mathematical contract](JET_VANISHING_MULTIPLICITY_INDEPENDENT_PRE_REVIEW.md). `JetVanishing a m h` is precisely vanishing of the first `h` **ordinary coefficients** of the reviewed `oddJetPolynomial` in `t=X²−1`. The first theorem applies `Polynomial.X_pow_dvd_iff` with no derivative or Taylor normalization. Under exact frozen even-Fourier vanishing and the explicit source-range bound `h≤m`, the reviewed odd Toeplitz identity turns this into `(X²−1)^h ∣ charpoly(T_(2m+1))`, including `X=0` and `h=0`.

The source factors `X²−1=(X−1)(X+1)`, uses monicity to establish that the actual characteristic polynomial is nonzero, and converts both polynomial divisibilities through `le_rootMultiplicity_iff` and `count_roots`. Its conclusion is **at least `h` copies of each `1` and `−1` in the characteristic-root multiset** used by the frozen `Empirical`, not a geometric eigenspace statement. The dependent finite-corrected-symbol corollary uses that exact source symbol and retains `hJet` as an explicit premise. The `m=0` premise forces `h=0`; no positive multiplicity is invented. This module gives no witness satisfying the jet equations, norm budget, final infinite symbol, nonextension, or empirical gap.

I independently ran a separate **imported** LeanCert audit under pinned Lean 4.33.1. It elaborated the public definition and four theorem signatures, ran `#assert_trust kernel` on all four, and printed transitive axioms. The audit exited 0; every theorem uses only `[propext, Classical.choice, Quot.sound]`. The source contains no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/SP14/JetVanishingMultiplicity.lean`** | **`a3b8f4911cf0786550b7739d2b4b9605ca8d13e7ca959959a3d2bd03acd1e723`** |
| Approved `JET_VANISHING_MULTIPLICITY_PRE_REVIEW.md` | `6af78ee310030425379eb0d15081fa1e6312d7787a8f3cbd1405f1f6cb9a432c` |
| Independent mathematical pre-review | `2e1b5d31ed60da4212e593f5d3eb42eeee3d4827388f59ac6ce6ea3fc0bd7fc6` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Canonical `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Imported `/private/tmp/sp14-jetmultiplicity-independent-audit.lean` | `dc64e647b154cbedcb9ba62490789dea925d5c1498687591fa4c75aea30b489b` |

Changed source or contract bytes reopen this review.
