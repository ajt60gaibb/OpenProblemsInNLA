# SP-14 odd-frequency Toeplitz characteristic polynomial: independent Lean review

**Reviewer:** `/root` (AI agent), 10 October 2026. **Verdict:** APPROVE frozen `OddFrequencyToeplitzCharpoly.lean` for its exact conditional finite-matrix identity. It does not prove the frozen negative `SP14.Target`.

I read the complete source and compared every public definition and theorem with the [approved mathematical contract](ODD_FREQUENCY_TOEPLITZ_CHARPOLY_INDEPENDENT_PRE_REVIEW.md). `OddFourierSupport a` says every even coefficient of the **actual frozen real-interval `FourierCoefficient`** vanishes. For section size `2m+1`, `oddB` has `(m+1)×m` entries at row-minus-column frequencies `2i−(2j+1)` and `oddC` has `m×(m+1)` entries at `(2i+1)−2j`. The proof reindexes the frozen `Toeplitz` by `baseParityEquiv m`, kills precisely the two same-parity blocks using this premise, and keeps the rectangular blocks in the source orientation. It covers all `m`, including `m=0`.

The reviewed off-diagonal block identity then gives `charpoly(T_(2m+1)) = X · Q_m.comp(X²)` with the **explicit** `Q_m=charpoly(oddC*oddB)`. The separate theorem `oddQuotient_zero` checks `Q_0=1`. Defining `R_m(t)=Q_m(t+1)` yields exactly `charpoly(T_(2m+1))=X · R_m.comp(X²−1)`, including `X=0`; no division by an eigenvalue or spectral regularity is used. This is the source's finite “no division ambiguity” algebra. The proof assumes even-frequency vanishing; it does not prove that the final infinite symbol has that support, its jet vanishing, the selected packet parameters, root multiplicity, nonextension, or the empirical gap.

I independently ran a separate **imported** LeanCert audit under pinned Lean 4.33.1. It elaborated the five public definitions and four theorem signatures, ran `#assert_trust kernel` on all four theorems, and printed their transitive axioms. The audit exited 0; every theorem uses only `[propext, Classical.choice, Quot.sound]`. The source contains no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/SP14/OddFrequencyToeplitzCharpoly.lean`** | **`aa6de57a4b247b81296d36fb2ed70f47d9c0b1863d0290792f6f3c16b3d4aff5`** |
| Approved `ODD_FREQUENCY_TOEPLITZ_CHARPOLY_PRE_REVIEW.md` | `55a5674b0f17f283d13f2a9d1b6b1ab1f18aca9faae5b8a21074acf9cc439382` |
| Independent mathematical pre-review | `63dcd09d388727543e9650197527e0b3571cf4fb645487b4049cbdce10a9fea8` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Canonical `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Imported `/private/tmp/sp14-oddcharpoly-independent-audit.lean` | `5ae2cb5893b949ae124d3e8e6fd9b64d4c042a62838aaff45887ec12d36194ee` |

Changed source or contract bytes reopen this review.
