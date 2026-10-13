# SP-14 two-mode first-smallness witness: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen strict first-background witness for aggregate import. It satisfies all five reviewed finite smallness conditions for any positive threshold; it does not establish the later packet stages, inverse bounds, or full SP-14 Target.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP14/TwoModeFirstSmallness.lean` | `fdce8c6847fe1a603251d4a20bdedea3e061ecc9683bbbe833a6e659c8327bd1` |
| Exact canonical first-smallness contract | `c763ef118c85bbf178fea605a0ef9693932d287ed6308207c53b883ce4f9a596` |
| Separate imported audit `/private/tmp/sp14-two-mode-first-smallness-independent-audit.lean` | `9c4d0aef3396db4ddf20bcc0d9d3cd743ea046d0ce4365286d386b45138c8ef3` |

The source uses the actual nonzero real two-mode corrections `P₋=ε(s⁻¹+s⁻²)` and `P₊=ε(s+s²)`, with same-length quotients `Q₋=εs⁻²` and `Q₊=εs`. Both contacts at `s=-1` hold separately. The literal finite norms are `W⁰(P₋)=2ε` and `W⁴(P₊)=97ε` (weights 16 and 81). The exact quotient and product bounds cost `C₀ε` and `A·3^(9/8)ε`, where `C₀=W⁰(g₀)` and `A=W^(9/8)(F)`. The actual curve bound is `2·2^(9/8)A(3^(9/8)+2^(9/8))ε + 2^(9/8)[2(2^(9/8)+3^(9/8))ε]²`; these are the reviewed constants and frequency shifts.

For any `γ>0`, the source chooses `ε=min(1,γ/(2D))` with exactly the reviewed positive `D=1+2+97+C₀+A·3^(9/8)+2·2^(9/8)A(3^(9/8)+2^(9/8))+4·2^(9/8)(2^(9/8)+3^(9/8))²`. The proof uses `ε²≤ε` and `Dε≤γ/2<γ` to obtain all five **strict** inequalities. The public theorem states the actual finite curve, both separate endpoint contacts, and the continuous quotient extension. It does not replace any literal Fourier size by an artificial coefficient bound.

The direct pinned Lean 4.33.1 module build passed 2,780 jobs. A separate imported audit checked all public definitions and the exact existential theorem, reran LeanCert kernel trust, and printed only `[propext, Classical.choice, Quot.sound]`. The source scan found no proof escape. Changed source bytes require a new review.
