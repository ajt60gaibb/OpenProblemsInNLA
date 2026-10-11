# TR-14 one-factor local Fourier decomposition: independent pre-review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen exact contract for implementation. It is a local multilinear factorization, with no CRT or global width conclusion.

| Reviewed input | SHA-256 |
| --- | --- |
| `LOCAL_ONE_FACTOR_FOURIER_PRE_REVIEW.md` | `9bfa860893d7a7d049ea1c9ced1a508d2c10eed430680e95bd2dee3e9e51cc91` |
| Canonical `TR-14/solution.tex` | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6` |
| Frozen `NLA.Statements.TR14` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Audited finite Fourier filter | `2e128ccd73ab653c9356ba478159af1af6d3fd8e728dec15ead29efd3728daea` |
| Audited local root | `ce623be5bde47e2e60c5198c31ac3215ed061d7b2a8d7d278e415390f9b1dc28` |

For `m≥3,ℓ≥1`, the genuine Frobenius condition gives the unique reversed element `u` and a root `w^m=u`. The canonical degree-`<ℓ` representative of each `w a_k` maps back to that local class. Therefore the product of all representatives maps to `u∏a_k`, whose top coefficient equals `Λ(∏a_k)`. Reduction modulo `z^ℓ` cannot change the coefficient at `ℓ−1`; this is the necessary quotient-to-polynomial bridge.

Each representative has degree at most `ℓ−1`, so the product has degree at most `m(ℓ−1)`. For `N=(m−1)(ℓ−1)+1`, the selected exponent is `ℓ−1` and the next congruent exponent is `m(ℓ−1)+1`, just outside the product's support. The previously audited primitive Fourier filter thus recovers exactly this coefficient with phase `((ζ^j)^(ℓ−1))⁻¹/N`. Evaluation of the polynomial product is multiplicative, giving the same linear functional `F_j(a)=R_ℓ(w a)(ζ^j)` in all `m` modes. There is no quotient evaluation at a nonzero root of unity.

At `ℓ=1`, the count is one and the identity is scalar; at `ℓ=2,m=3`, degrees one and four check the phase and cutoff. The document correctly excludes `m=1` for `ℓ>1`, where its one-node formula is false, and preserves the final target's `m≥3`. The mode map `Σ_i v_i(α+z)^i` uses zero-based coordinates with no bound `ℓ≤n`, binomial multiplier, or conjugation. It identifies a later route to the actual symmetric tensor factors but does not claim a width witness without CRT and the all-moment bridge.

Implementation must expose complex-linear local factors, justify full finite coefficient expansion for polynomial evaluation, keep `m≥3` and `ℓ≥1`, and stay unimported until a separate source/signature/LeanCert audit. No change to canonical IDs, READMEs or frozen Target is approved.
