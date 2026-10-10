# TR-14 local Fourier coefficient filter: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen narrow Fourier source for aggregate import. It proves the exact local coefficient filter and node count, not a CRT decomposition, symmetric width bound, or frozen `Target`.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/TR14/LocalFourierFilter.lean` | `2e128ccd73ab653c9356ba478159af1af6d3fd8e728dec15ead29efd3728daea` |
| Exact local Fourier upper contract | `7466b599503bcca7dbe9f99e784acdf2b0a2569b80b7f1c4baf1dcd148b87351` |
| Independent mathematical pre-review | `e335efd8707352413d9219464730f89aa882f6059c9aead7624a79cb3132c248` |
| Canonical `solution.tex` | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6` |
| Frozen `NLA.Statements.TR14` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Separate imported audit `/private/tmp/tr14-localfourierfilter-independent-audit.lean` | `224fc045e5f1e6f8b5c174743b5cf53d40730346e04a6e672900f78848df5ef5` |

The source defines the exact number `N=(m−1)(ℓ−1)+1`, proves `N>0` and the required `ℓ=1` endpoint `N=1`. Its finite geometric sum over powers of a primitive `N`th complex root is `N` when `N` divides the exponent and zero otherwise. For `0≤k≤m(ℓ−1)`, the shifted exponent `k+N−(ℓ−1)` is positive and below `2N`; divisibility therefore occurs only at `k=ℓ−1`. This is exactly the source's unique-congruence argument, including the upper endpoint and `ℓ=1`.

Finite sum rearrangement then proves the coefficient identity for **every** vector through degree `m(ℓ−1)`. A separate phase lemma converts the positive exponent `N−(ℓ−1)` into the canonical inverse character `(ζ^j)^(−(ℓ−1))`; the inverse-character theorem has the precise factor `1/N` and no conjugation. A primitive root exists for every positive `N`, so no genericity or existence premise is added to a future application. The statement remains independent of CRT and tensor semantics.

The pinned Lean 4.33.1 direct module build passed 3,008 jobs. My separate imported LeanCert audit exited zero, checked the exact public signatures, reran `#assert_trust kernel`, and printed only `[propext, Classical.choice, Quot.sound]` for the sum, cutoff, inverse-character, and primitive-root existence theorems. A frozen-source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape. Changed source bytes require a new review.

CRT factorization, local Frobenius roots, mode-to-moment bridge, symmetric width construction, the second upper bound, arbitrary ordinary lower bound, and full TR-14 Target remain open.
