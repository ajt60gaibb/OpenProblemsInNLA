# RA-20 — Critical-point counts for symmetric rank-two approximation with diagonal zeros

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Topic:** Symmetric structured low-rank approximation  
**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Solved  
**Last checked:** 2026-09-11

**Rating rationale:** Historical rating of the proposed all-order formulas. The negative resolution below is elementary; it does not establish corrected formulas in the remaining cases.

## Negative resolution - 2026-09-11

The displayed universal conjecture is false: **$`e_{3,3}=3`$, whereas its formula gives** $`4`$. For $`n=s=3`$, write the off-diagonal entries as $`(a,b,c)`$. The determinant is $`2abc`$, so the variety is the union of three coordinate planes. Each smooth component has exactly one simple critical point for generic full-Frobenius data. Their intersections are singular and are excluded by the definition below.

[Complete proof](solution.md) · [Proof PDF](solution.pdf) · [Standalone TeX](solution.tex) · [Independent audit and exact verification](../../references/research-expansion-2026-09-11/ra20-resolution/README.md).

This counterexample was identified and independently checked during the Codex maintainer audit. It is automated-agent verification, not external human peer review or formal certification. The source's Table 7 repeats the value $`4`$; this is not a transcription error in the entry. The complete original target, including its dimension range and all four formulas, is retained below. No conclusion about corrected formulas or the other parameter cases is claimed, and no priority claim is made.

## Statement

For $`s\in\{1,2,3,4\}`$ and $`n\ge\max\{3,s\}`$, define

```math
W_{n,s}=\{X\in\mathbb C^{n\times n}:X^{\mathsf T}=X,
\ \mathop{\mathrm{rank}}\nolimits X\le2,\ x_{11}=\cdots=x_{ss}=0\}.
```

For generic symmetric $`U\in\mathbb C^{n\times n}`$, let $`e_{n,s}`$ be the number of complex critical points on the smooth locus of $`W_{n,s}`$ of

```math
d_U(X)=\sum_i(x_{ii}-u_{ii})^2+
2\sum_{i< j}(x_{ij}-u_{ij})^2.
```

Generic means outside a proper algebraic exceptional set. A point is critical if the differential vanishes on its tangent space. Thus $`e_{n,s}`$ is the Euclidean distance degree for the bilinear extension of the **full Frobenius metric**; the off-diagonal terms have weight two, and complex conjugation is absent.

**Conjecture (Kubjas–Sodomaco–Tsigaridas, Conjecture 5.6, $`n\ge3`$).**

```math
e_{n,s}=\begin{cases}
3(n-1)-2,&s=1,\\
9(n-2)-2,&s=2,\\
27(n-3)+4,&s=3,\\
81(n-4)+28,&s=4.
\end{cases}
```

All four zero counts form one target. The explicit $`n\ge3`$ restriction avoids a degenerate endpoint in the printed statement: when $`n=2`$, the rank bound is vacuous and both possible varieties are linear with ED degree one, whereas the displayed $`s=2`$ formula does not apply.

## Evidence and numerical significance

The source's Table 7 reports values matching its formulas through order ten, but the $`n=s=3`$ value conflicts with the exact calculation above. The table therefore cannot establish the conjecture's validity. The problem counts stationary candidates for symmetric Frobenius approximation with prescribed diagonal zeros. It concerns fixed rank two, unlike [corank-one approximation in general square matrices](../RA-19/README.md).

## References and status check

- K. Kubjas, L. Sodomaco and E. Tsigaridas, *Exact solutions in low-rank approximation with zeros*, Linear Algebra and its Applications 641 (2022), 67–97. [DOI](https://doi.org/10.1016/j.laa.2022.01.021); [current author manuscript](https://arxiv.org/abs/2010.15636v2), 29 January 2022. Conjecture 5.6 and Table 7, manuscript p.21; §2 and §5 supply the distance convention.

The initial literature search on 2026-09-11 found no later resolution and compared the formulas with Table 7. The subsequent independent maintainer audit supplied the counterexample above, superseding the initial Open classification. Excluding $`n=2`$ does not remove the admissible counterexample $`n=s=3`$. The separate nonsymmetric formulas in Conjecture 5.2 have a table/label discrepancy and are not imported here. The permanent ID, original target and canonical path are retained.
