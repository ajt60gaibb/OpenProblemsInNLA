# SP-14 endpoint Wiener cancellation: independent pre-review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the revised frozen contract for staged implementation. This is one source-accurate Wiener component, not the two-level operator proposition or the negative Target.

| Reviewed input | SHA-256 |
| --- | --- |
| `ENDPOINT_WIENER_CANCELLATION_PRE_REVIEW.md` | `6bd5adcd58819b4ad585bb25fd565ee33453c51c341e58e1ccf136a6cbfe9175` |
| Canonical `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Frozen `NLA.Statements.SP14` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Audited `BaseExteriorFactor.lean` | `a8dbc23e8544378ab504ff8130387701fa0270cb2753555c0f05b71057d316dd` |
| Audited `FiniteLaurentBackground.lean` | `21ddde26cfbbfec236f7c9ddc3b212702baa56c0ceef333e9289f09f5a052e7b` |

The coefficient recurrence is exact: for `c_n=binom(1/2,n)`, `c_(n+1)=((1/2−n)/(n+1))c_n`, so `(n+1)(c_n+c_(n+1))=(3/2)c_n`. It gives `d_0=3/2`, `d_1=3/8`, `d_2=−1/16` by rational arithmetic. The expected `|c_n|=O((n+1)^(-3/2))` gives `|d_n|=O((n+1)^(-5/2))`; multiplying by the exact source weight `(n+1)^(9/8)` leaves a convergent exponent `−11/8`. That asymptotic estimate remains a proof obligation, not an imported premise. Multiplication of `g₀(s)=Σc_ns^(-n)` by `1+s` yields the literal coefficient pattern `F_1=1`, `F_(−n)=d_n`, and no overlapping frequency at zero; therefore the proposed norm formula has exactly the `2^(9/8)` positive-frequency term.

For `P₋=Σ_{j=1}^u p_j s^(−j)`, writing `Q₋=Σ_{j=2}^u q_j s^(−j)` yields `p_j=q_j+q_(j+1)` with `q_1=q_(u+1)=0`. The consistency condition is exactly `P₋(-1)=0`; `u=0,1` force zero, and `t(s⁻¹+s⁻²)=(1+s)ts⁻²` checks the nonempty orientation. Since `F` has maximal frequency `+1` and `Q₋` maximal frequency `−2`, their product has only strictly negative frequencies. The bilateral weight `(1+|j|)^(9/8)` is submultiplicative, so the claimed convolution inequality has constant one. Because `F_1=1`, its norm is positive, and `‖Q₋‖<2^(-1000)/‖F‖` indeed forces **this one** source hypothesis `‖g₀P₋‖<2^(-1000)`.

The source's two-level proposition leaves `γ` unspecified, while its later explicit-parameters corollary sets `γ=2^(-1000)`. The revised contract now makes that distinction. Identifying the coefficient sequences with the frozen Fourier integral, weighted summability, finite endpoint factorization, and the convolution estimate require Lean proofs; no such claim is approved by this document alone. The other four smallness inequalities, simultaneous background choice, operator inverse bounds, and full SP-14 Target remain open.
