# Final probability-budget absorption

Exact contract proposed and approved by root before implementation, 2026-10-06. This is a scalar consequence of the already proved Gaussian denominator estimate; it introduces no new stochastic premise and no computed dimension cutoff.

For every real $\alpha>0$, put $\beta=\alpha+4$, $a=\alpha+6$, and let $q$ be the actual `gaussianUnitIntervalMass`. Prove that eventually for natural $n$,

$$
 \operatorname{ofReal}(e^{-(\beta-2)\log n})
 +(2n^2+n+2n^3)\operatorname{ofReal}(e^{-a\log n})
 +\operatorname{ofReal}(q^{n^2})
 <\operatorname{ofReal}(n^{-\alpha}).
$$

The polynomial coefficient on the left is interpreted in ENNReal. All powers of natural $n$ in that coefficient are natural powers; $n^{-\alpha}$ is the real rpow.

Use `gaussian_entryMax_lt_one_eventually (α+1)` together with the exact `gaussian_entryMax_lt_one_probability` identity to bound the third term strictly by `ofReal (n^(-(α+1)))`. For $n\ge4$, the first term is $n^{-\alpha}/n^2$, the second is at most $5n^{-\alpha}/n^3$ because $2n^2+n+2n^3\le5n^3$, and the third comparison term is $n^{-\alpha}/n$. Thus the total coefficient is at most $1/16+5/64+1/4=25/64<1$. These inequalities are symbolic and preserve strictness. Dimension zero is excluded only by the eventual $n\ge4$ bound; no extra final theorem assumption is introduced.

Root's explicit preimplementation approval requested the new module `FinalFailureScalars.lean` with this exact contract. The final exact source and its kernel dependency audit will receive a separate independent review.
