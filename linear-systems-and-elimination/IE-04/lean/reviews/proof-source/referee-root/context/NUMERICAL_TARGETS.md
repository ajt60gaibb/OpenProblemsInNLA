# IE-04 proposed exact quantitative obligations

Draft mathematical statements only. This file is not yet a reviewed or frozen
Lean Challenge, and contains no proof implementation.

Use zero-based indices `i,j : Fin n`, with `n ≥ 2`:

`Wₙ(i,j) = 1` if `j = n−1`; otherwise `1` if `i=j`, `−1/2` if
`j<i`, and `0` if `i<j`.

For stage `k=0,...,n−1`, let `cₖ=(3/2)^k`,
`Bₙ=2^(n+2)`, `δₙ=1/2^(n²+n+1)` and `Kₙ=n²(n²+n+5)`.
All these powers except the final tail's real powers have natural exponents.

1. **Unperturbed path:** The actual no-swap active matrix at stage `k` is zero
   outside its active block, has the original triangular pattern in nonfinal
   columns, and has value `cₖ` in every active final-column entry. Its current
   pivot is `1` for `k<n−1`, all competitors are `−1/2`; the last pivot is
   `cₙ₋₁`. Its actual growth is `cₙ₋₁`.
2. **Budget identities:** `0<δₙ≤1/8`, `1≤cₖ≤2^n` for `k<n`, and
   `Bₙ^(n−1) δₙ = 1/8`. For `k<n`, `Bₙ^k δₙ≤1/8`.
3. **Quotient bound:** If `0≤e≤1/8`, `|p−1|≤e`, and `|a+1/2|≤e`, then
   `p≥7/8`, `|a|≤5/8`, `|a/p|≤5/7`, and `|a/p+1/2|≤2e`.
4. **Schur error:** If the current active entries are within `e` of the model
   entries, the diagonal pivot has the strict gap above and
   `|model pivot-row entry|≤2^n`, every updated entry is within
   `(2+2^(n+1))e≤Bₙe`. The actual current pivot choice is uniquely no-swap.
5. **Full-box robustness:** If `∀i j, |A(i,j)−Wₙ(i,j)|≤δₙ`, then for every
   `k<n` the actual no-swap trajectory differs from the model active matrix by
   at most `Bₙ^k δₙ`. The path is admissible, all its pivots are positive,
   every admissible path equals it, and `det A≠0`.
6. **Growth bridge:** Every such `A` has input maximum `≤1+δₙ≤9/8`, final
   active pivot `≥cₙ₋₁−1/8`, and therefore actual GEPP growth
   `≥(8 cₙ₋₁−1)/9≥7 cₙ₋₁/9>cₙ₋₁/2`. The input maximum is proved positive
   before dividing.
7. **One density constant:** For every real `z∈[-2,2]`, the actual standard
   normal density `(2π)^(-1/2) exp(−z²/2)` is `>1/32`. A fixed analytic
   `exp(1)<3`, `π<4` bound suffices; no integration certificate is assumed.
8. **Scalar interval:** For every `a∈[-1,1]` and `0<δ≤1/8`,
   `gaussianReal 0 1 [a−δ,a+δ] ≥ δ/16` (as a real probability or the
   equivalent `ENNReal.ofReal` statement).
9. **Product box:** If all `G(i,j)` have the stated product law, then
   `Pr{∀i j, |G(i,j)−(Wₙ(i,j)−Iₙ(i,j))|≤δₙ}` is the product of the scalar
   interval measures and is at least
   `(δₙ/16)^(n²) = 1/2^Kₙ`.
10. **Actual event inclusion:** This measurable Gaussian rectangle is contained
    in the event that `Iₙ+G` is nonsingular and every admissible GEPP path has
    growth `>cₙ₋₁/2`. The actual first-available algorithm is one such path.
11. **Universal probability bound:** For every integer `n≥2`,
    `Pr{det(Iₙ+G)≠0 ∧ firstGrowth(Iₙ+G)>cₙ₋₁/2} ≥ 1/2^Kₙ`.
12. **No fixed polynomial dominates:** For every real `c₁,c₂>0`, there is
    `n≥2` such that, setting `xₙ=cₙ₋₁/(2 n^c₁)`, both `xₙ≥1` and
    `c₂ xₙ>Kₙ` hold. Here `n^c₁` is the real power of positive `n`.
13. **Strict tail violation:** For this `n,xₙ`, actual spectral norm
    `‖Iₙ‖₂=1`, noise level `σ=1`, and
    `Pr{det(Iₙ+G)≠0 ∧ firstGrowth(Iₙ+G)>xₙ n^c₁}
      > 2^(-c₂ xₙ)`.
14. **Canonical conclusion:** No positive universal pair `c₁,c₂` satisfies the
    complete original tail proposition for every dimension, every center with
    spectral norm at most one, every allowed noise scale, every threshold
    `x≥1`, and every admissible tie rule. State and prove its reduction to the
    first-available rule explicitly; retain the all-path strict-box result.

Nonsingularity of padded active matrices is not a valid obligation: only their
active blocks are invertible. Gaussian realizations outside the certified box
need no growth analysis. If a total growth function assigns a convention to
singular inputs, the event explicitly includes input nonsingularity and its
relation to the repository's probability convention must be recorded. No
almost-sure tie or determinant claim should be asserted without a proof when
using it to identify two probability expressions.

## Draft declaration boundary

The corresponding independent Challenge has 21 exports. In addition to the
quantitative items above, explicit obligations establish actual finite-maximum
semantics, a nonempty measurable admissible rule class, the Gaussian probability
measure, and measurable tail events. The complete negative conclusion remains
`NLA.IE04.not_uniformExponentialTail`; the box certificate is not its replacement.
The frozen package has not yet been approved or elaborated.
