# MF-03 — A uniform disk bound for wave-kernel Padé approximants

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** hard  
**Importance:** interesting to specialist  
**Status:** open; original conjecture plus a search for subsequent resolution  
**Last checked:** 2026-09-08  

## Problem statement

Let

$$
f(z)=\sum_{j=0}^\infty\frac{z^j}{(2j)!}=\cosh\sqrt z,
$$

where the series defines the entire function without a square-root branch choice.
For each integer $m\ge1$, let $r_m=P_m/Q_m$ be its diagonal Padé
approximant at zero: $\deg P_m,\deg Q_m\le m$, $Q_m(0)=1$, and
$Q_m(z)f(z)-P_m(z)=O(z^{2m+1})$. Is it true that the reduced rational
function $r_m$ has no pole in $\{z\in\mathbb C:|z|\le3\}$ and

$$
|1-r_m(z)|\le2\qquad (|z|\le3)
$$

for every $m$?

## Reference and status evidence

Nadukandi and Higham,
[Computing the Wave-Kernel Matrix Functions](https://eprints.maths.manchester.ac.uk/2651/3/manuscript_nadukandi_higham_wkm_2018_08_01.pdf),
SIAM J. Scientific Computing 40(6) (2018),
[DOI](https://doi.org/10.1137/18M1170352), §4.2, Conjecture 4.6,
manuscript p. 12. Lemma 4.5 establishes the finite range $m\le20$;
§4.3 explains its role in backward-error analysis. Searches for the paper title
with “conjecture” and for “Conjecture 4.6” with “cosh” and “Padé” located no
general proof or counterexample. The status evidence is therefore weaker than a
recent paper explicitly reaffirming the conjecture.
