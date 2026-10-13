# TR-14 local CRT/Fourier count and width: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE these two frozen modules for aggregate import. They prove the reviewed normalized-chart node count and one symmetric upper construction, not the complete TR-14 Target.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/TR14/LocalCRTFourierCount.lean` | `9505894e469504e10cc887806e8a2820ccfbf8abebfbd18e66e6c459c1deb027` |
| `lean-statements/NLA/Proofs/TR14/LocalCRTFourierWidth.lean` | `8359bed454116aa646f292050454b0e7ea39520e293826a8be5d31ac5ddcde3c` |
| Exact global Fourier contract | `9a2f693fd8ad6be0a26b0dc1d2d88e0afc65adf32dd9cf2b386aaf074aa954ee` |
| Separate imported audit `/private/tmp/tr14-local-crt-fourier-width-independent-audit.lean` | `39dc5cbc5974ff6c212980656ca657442b79ac8340a867a5b47f5cf393d36e13` |

The count module uses the actual dependent node family `Σ α : LocalRootIndex g, Fin (localFourierCount m ℓα)`. Its cardinal is the sum of local counts. For `m≥3` and each positive multiplicity, `localFourierCount m ℓα+(m−2)=(m−1)ℓα`. Summing and using the already audited root multiplicity sum yields the exact natural-number formula `(m−1)*g.natDegree−(m−2)*|S|`. This retains repeated roots and justifies the subtraction arithmetically.

The width module reindexes the existing exact all-coordinate Sigma identity by an actual `Fintype.equivFin` and builds the **frozen** `NLA.Statements.TR14.SymmetricWidth`. Its unconditional construction from a supplied Sigma identity is followed by the least-monic-apolar corollary with explicit `m≥3`, `n≥2`, nonzero moment vector, positive bounded degree, apolarity, and all lower apolar kernels zero. The corollary applies the audited global Sigma theorem and the count formula; no assumed genericity or extra scaling enters.

The direct pinned Lean 4.33.1 builds passed 3,430 and 3,431 jobs. A separate imported audit checked the public signatures and LeanCert kernel trust, with only `[propext, Classical.choice, Quot.sound]`. Source scans found no proof escape. Changed source bytes require a new review. The original-coordinate projective root correspondence, second upper construction, lower bounds, and all-width equivalence remain open.
