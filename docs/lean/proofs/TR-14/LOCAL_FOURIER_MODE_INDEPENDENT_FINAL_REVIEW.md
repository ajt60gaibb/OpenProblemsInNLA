# TR-14 local Fourier mode coordinates: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen source for aggregate import. It turns the reviewed one-factor local formula into exact zero-based mode-vector coordinates, without a global CRT or width conclusion.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/TR14/LocalFourierMode.lean` | `ab77987b8b5448ef24f59ca6c49a2598011f3b13babda48ca9cb09febe2c6626` |
| Exact one-factor/mode pre-implementation contract | `9bfa860893d7a7d049ea1c9ced1a508d2c10eed430680e95bd2dee3e9e51cc91` |
| Independent mathematical pre-review | `54fcc3fcd79b8788f9962729673e9933a2fb180b37bd8f3e6c92d36536e01a3e` |
| Audited one-factor source | `3b0e9c148f6a01c6392c370c5949d4ab4ccd84552d1844cec7aa3ebef084f516` |
| Separate imported audit `/private/tmp/tr14-localmode-independent-audit.lean` | `2b06bf5e0532c593dc89420ed8bd7c08e04f1df29d33653e06918327cd4b8b98` |

The complex-linear map is the actual zero-based polynomial substitution `v↦Σ_{i∈Fin n}v_i(α+z)^i` in `ℂ[z]/(z^ℓ)`, for arbitrary `ℓ>0`; it never assumes `ℓ≤n`. On a coordinate basis vector it returns exactly `(α+z)^i`. Composing with each local remainder-evaluation factor gives a complex-linear functional whose coordinate vector is `V_j(i)=F_j((α+z)^i)`. The proof expands every factor as `Σ_i v_i V_j(i)`, with no conjugation or binomial multiplier.

The public tensor-coordinate theorem applies the audited one-factor identity to the modes `(α+z)^(i_k)` and uses the **same** coordinate vector in all `m` factors. It retains `m≥3`, `n≥2`, `ℓ>0`, a genuine Frobenius functional, the exact primitive node count, and every `Fin m→Fin n` multi-index. The `n≥2` premise mirrors the frozen target and does not restrict the local multiplicity.

The pinned Lean 4.33.1 direct module build passed 3,422 jobs. My separate imported LeanCert audit exited zero, checked the linear map, basis and expansion signatures plus the public coordinate theorem, reran kernel assertions, and printed only `[propext, Classical.choice, Quot.sound]` for the main result. A frozen-source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape. Changed source bytes require a new review.

The global quotient's CRT decomposition and local functional transfer, summation of node counts, symmetric upper width, arbitrary ordinary lower width, and full TR-14 Target remain open.
