# TR-14 dependent root/Fourier coordinate sum: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen dependent-node module for aggregate import. It gives an exact finite symmetric coordinate formula under actual least-apolar hypotheses; the count, frozen width witness, and full Target remain open.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/TR14/LocalCRTFourierSigma.lean` | `7fbefd26bafe5549e56d3e79ac0b75d55e859cf032d8ac8308a1c45f9f03f9f1` |
| Corrected exact global-Fourier contract | `9a2f693fd8ad6be0a26b0dc1d2d88e0afc65adf32dd9cf2b386aaf074aa954ee` |
| Independent mathematical pre-review `LOCAL_CRT_FOURIER_GLOBAL_INDEPENDENT_PRE_REVIEW.md` | `3e6c2c358d3fb1aab9564f3bb609926c0173a21e1866269e8e294bb6321c2ac3` |
| Separate imported audit `/private/tmp/tr14-local-crt-fourier-sigma-independent-audit.lean` | `b37011398f3844b19715313171b9a0ff6d5f505616bdf5a24d40572f3e5c60c8` |

The dependent node type is exactly `Σ α:LocalRootIndex g, Fin(localFourierCount m ℓα)`. Its coefficient is the audited inverse character `Nα⁻¹*((ζα^j)^(ℓα−1))⁻¹`, and its `Fin n→ℂ` vector uses the audited local mode construction with exact positive multiplicity. The same vector is used in every tensor mode. Under genuine local Frobenius, the source chooses the local nth-root and primitive-root witnesses per indexed root, applies the audited local Fourier formula to each exact CRT Hankel summand, and reindexes the nested finite sums by the dependent node type. The stronger theorem derives local Frobenius from the audited global quotient Frobenius theorem using `h≠0`, positive monic least-apolar degree, actual apolarity and all lower-kernel zero conditions; no unproved local nondegeneracy premise remains in that theorem. The coordinate equality holds for every zero-based frozen tensor index, including repeated roots and local multiplicity greater than mode dimension.

The pinned Lean 4.33.1 direct module build passed 3,429 jobs. My separate imported LeanCert audit exited zero, checked the node/coefficient/vector definitions and both public theorem signatures, reran `#assert_trust kernel`, and printed only `[propext, Classical.choice, Quot.sound]`. The frozen source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape. Changed source bytes require a new review.

Exact node-count arithmetic, reindexing by `Fin` to construct `SymmetricWidth`, original projective-root multiplicity correspondence, other upper/lower bounds, and the complete TR-14 Target remain open.
