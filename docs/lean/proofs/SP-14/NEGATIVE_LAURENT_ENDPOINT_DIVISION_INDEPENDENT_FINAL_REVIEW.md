# SP-14 finite negative Laurent endpoint division: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen source for aggregate import. It derives an exact same-index finite factorization from the actual contact equation; no weighted convolution or SP-14 Target follows yet.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP14/NegativeLaurentEndpointDivision.lean` | `d4d6fddadfa9d2b306faf88ca03a4cda0391fc59130d89db9ab914c970ffb19b` |
| Exact pre-implementation contract | `1d8f584838935b6ebc314bb5a12a3e5b981001ad1a045e1ea8dd7317c03ccbaa` |
| Independent mathematical pre-review | `5308d5e303abdedd99f750eb821d502d691a4d0a9e37ec3f980334b915232d3c` |
| Separate imported audit `/private/tmp/sp14-negative-endpoint-independent-audit.lean` | `265f7a3cc805a220c968065923abf39699e3c4580adb993c5be99ba3925fd11c` |

The proof uses the audited strict negative Laurent sum with one-based powers. Its real recurrence has `q₀=0` and `q_{j+1}=p_j−q_j` in zero-based coefficient notation. The finite telescoping identity leaves one virtual terminal coefficient `q_u s^{-u}`; evaluating the actual source at `s=-1` and using the contact hypothesis forces `q_u=0`. The returned `Fin u` vector consists of `q₀,…,q_{u−1}`, has first coefficient zero, and satisfies `P(s)=(1+s)Q(s)` for every circle point. This handles `u=0`, `u=1`, and `u=2` without a separate nonempty assumption or division by `1+s` at the contact point.

The pinned Lean 4.33.1 direct module build passed 2,624 jobs. My separate imported LeanCert audit exited zero, checked the exact public signature and frozen `negativeLaurent` definition, reran `#assert_trust kernel`, and printed only `[propext, Classical.choice, Quot.sound]`. A frozen-source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape. Changed source bytes require a new review.

Fourier coefficients of the product with the base factor, weighted convolution, the five smallness estimates, background inverse, nonlinear counterexample, and full SP-14 Target remain open.
