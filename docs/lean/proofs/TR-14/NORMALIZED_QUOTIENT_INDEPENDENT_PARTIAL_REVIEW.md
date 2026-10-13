# TR-14 normalized quotient: independent partial Lean review

**Reviewer:** `/root` (AI agent), 10 October 2026. **Verdict:** APPROVE frozen `NormalizedQuotient.lean` for the conditional monic quotient functional and its exact all-moment recurrence. This is a proper part of the [approved quotient/Frobenius contract](QUOTIENT_FROBENIUS_INDEPENDENT_PRE_REVIEW.md); it proves neither Frobenius nor the global `TR14.Target`.

I read the complete source and compared the public signatures with the frozen apolar convolution and canonical §2 recurrence. For a monic polynomial `g` of degree at most `D`, `quotientMomentFunctional` uses the power basis of the genuine quotient `AdjoinRoot g` and assigns its first `deg g` basis powers the matching moments. The quotient's complex dimension is exactly `deg g`. The source derives the root relation from `g(root g)=0`, multiplies it by each power, and maps it through the functional. `MonicMomentRecurrence` quantifies over every `k` with `k+deg g≤D`; `monicMomentRecurrence_of_apolar` gets those equations from the exact `IsApolar` map, using the leading coefficient one. Strong induction then proves `λ((root g)^j)=h_j` for **every** `0≤j≤D`, including the first recurrence at `j=deg g` and final moment `j=D`. There is no use of moments beyond `D`.

The public `normalized_quotient_all_moments` retains a **monic affine apolar polynomial as a premise**. It does not require minimality because full moment matching already follows from monicity and apolarity; it also does not assert a nondegenerate pairing. A homogeneous minimal apolar form can have its top coefficient zero, so the still-missing `GL₂` chart transport or coordinate-free equivalent must discharge that premise for arbitrary original data. The Frobenius radical argument, original-coordinate middle catalecticant rank, mode-product identity, and arbitrary ordinary-width lower bound remain open.

I independently ran a separate **imported** LeanCert audit under pinned Lean 4.33.1. It elaborated the two public definitions and five public theorem signatures, ran `#assert_trust kernel` on each, and printed transitive axioms. The audit exited 0; every result uses only `[propext, Classical.choice, Quot.sound]`. The frozen source contains no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/TR14/NormalizedQuotient.lean`** | **`3c6809e84eb522ad82c28f49245b80ef6da7da84cd201f46f4cbfb54a363a54d`** |
| Approved `QUOTIENT_FROBENIUS_PRE_REVIEW.md` | `3b8d8d1484755f149c61feb992255c6be617f659219eb0c1bf96b165c0134eea` |
| Independent mathematical pre-review | `083891fa88ba124a82b9548619bb35674c7b2ad728dc6d9c4469668e555922e7` |
| Frozen `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Canonical `solution.tex` | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6` |
| Imported `/private/tmp/tr14-normalizedquotient-independent-audit.lean` | `ab4ebb3ea00dbbc55369bdbbcfe7fe6ecedbf33b455f931ef58b2a2b90376ea8` |

Changed source or contract bytes reopen this review.
