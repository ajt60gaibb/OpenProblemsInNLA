# TR-14 apolar map and minimal degree: independent Lean review

**Reviewer:** `/root` (AI agent), 10 October 2026. **Verdict:** APPROVE frozen `ApolarMinimal.lean` for the exact finite apolar convolution and least nonzero degree. This is a partial foundation, not a proof of `NLA.Statements.TR14.Target`.

I read the full source and compared its elaborated public signatures with the [approved mathematical sub-contract](APOLAR_MINIMAL_INDEPENDENT_PRE_REVIEW.md) and the canonical source's `I_d`. For every `d≤D`, `apolarMap` sends a homogeneous coefficient vector `g : Fin(d+1)→ℂ` to the complete vector of equations `Σ_{i=0}^d g_i h_{i+j}` for `0≤j≤D−d`, proving the `i+j≤D` index bound. `IsApolar` means exactly that this map is zero. No affine monic or nonzero top-coefficient condition is imposed, so forms with a root at infinity remain included.

The degree-zero equivalence includes every moment and proves that a nonzero moment vector has no nonzero constant apolar vector. At `d*=⌊D/2⌋+1` for `D≥1`, the source uses finite-dimensional rank-nullity and the strict dimension inequality to produce a nonzero kernel vector for every `h`. Least-number selection then yields `1≤r₀≤d*`, a nonzero vector in `I_{r₀}`, and zero kernel at **every** lower degree, including degree zero. The final arithmetic theorem retains both `D=2r₀−2` and `D≥2r₀−1` branches. The zero moment vector is excluded only from the least-degree package, as in the reviewed contract; the apolar map itself remains defined for it. The Frobenius quotient, middle catalecticant rank, and arbitrary ordinary-width lower bound remain open.

I independently ran a separate **imported** LeanCert audit under pinned Lean 4.33.1. It elaborated both public definitions and all five theorem signatures, ran `#assert_trust kernel` on the map and every theorem, and printed their transitive axioms. The audit exited 0; each result uses only `[propext, Classical.choice, Quot.sound]` or a subset. The source contains no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/TR14/ApolarMinimal.lean`** | **`0e98ae3b414d2130bebe7470a25c7c8b3e422225b5581ae4b93d036f39f520d9`** |
| Approved `APOLAR_MINIMAL_PRE_REVIEW.md` | `93908b1804fdd4f2504382e59a6a2b2d50b5544e5c139d37ace3f530b30a4b23` |
| Independent mathematical pre-review | `b255d6982d1c16007e53ded006aa456f4eee89a48eebff2a8da858007815fb10` |
| Frozen `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Canonical `solution.tex` | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6` |
| Imported `/private/tmp/tr14-apolar-independent-audit.lean` | `b7b100088662f4487bb39c8a20e0df1964f718f5bdba79083eb4a47298048723` |

Changed source or contract bytes reopen this review.
