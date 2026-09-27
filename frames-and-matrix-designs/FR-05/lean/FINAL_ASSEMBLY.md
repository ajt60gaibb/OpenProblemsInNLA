# Completed FR-05 assembly

`Solution.lean` exports:

- `NLA.FR05.phaseRetrieval_injective_probability_le_inv`:
  $\exists C>0,\ \forall d\ge2,\ p_d\le C/d$.
- `NLA.FR05.phaseRetrieval_injective_probability_tendsto_zero`:
  the original FR-05 target $p_d\to0$.

The probability uses the unchanged iid standard complex-Gaussian frame law
with `4d-5` rows and the unchanged all-signals phase-retrieval predicate.
There are no analytic hypotheses or unproved intermediate estimates.

## Final argument

Write $\mu$ for the original Gaussian law, $E$ for its injectivity event,
and $P_g$ for the Haar-planted law. The sampler/density bridges prove
$P_g(E)=\int_E L_g\,d\mu$ and $p_M=\int_E L_r\,d\mu$.
The reference transformation is invertible, and the planted dimension
relabelling preserves the exact event. Event-local Cauchy–Schwarz gives

```math
p_M \le P_g(E)+\left|\int_E(L_g-L_r)\,d\mu\right|
\le P_g(E)+\sqrt{p_M\int(L_g-L_r)^2\,d\mu}.
```

Propositions 3.1 and 3.2 supply, beyond the maximum of their thresholds,

```math
p_M\le a/M^2+\sqrt{b p_M/M}.
```

The checked numerical reduction bounds this by $(2a+b)/M$.
Absorbing the finite prefix using $p_M\le1$ gives a single $C>0$ valid
for every $M\ge2$. Squeezing between zero and $C/M$ proves the limit.

`NLA/FR05/Measure/Comparison.lean` contains the measure-theoretic inequality;
`NLA/FR05/FinalAssembly.lean` connects the actual laws, propositions, and reduction.
The proof follows Li's frozen manuscript; no independent mathematical novelty
or specialist review is claimed.

## Verification scope

The full local Lean build and transitive axiom audit pass. Both final exports
depend only on `propext`, `Classical.choice`, and `Quot.sound`; neither depends
on the isolated `Challenge.lean` placeholders. Both the quantitative target
and original limit are included in `comparator.json`; the quantitative
challenge statement is unchanged, and the limit has its own matching fixture.
See [the local audit](verification/library-cleanup/README.md).

Independent statement review and the repository's isolated Linux
Comparator/kernel verification have not been performed for this completed
assembly. The catalog status remains `Solution claimed` pending those gates.
