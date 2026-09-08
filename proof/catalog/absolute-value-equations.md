# Absolute value equations and their conditioning

> Legacy source map and screening notes. Admitted statements have moved to category/problem folders. Follow the links below or [browse the new index](../../CATALOG.md). Shared notation and uncounted material are retained here as the historical source record.

This chapter contains **3 admitted problems**. Ratings are editorial. Status checks were performed on **2026-09-08**; a bounded literature search cannot certify that a problem remains unsolved.

Absolute values and vector inequalities are componentwise. All algorithmic questions below use rational input in binary and the deterministic Turing model. Input length includes the matrix dimensions and the bit lengths of all rational coefficients.

For a real square matrix $A$, define the diagonal perturbation family

$$
\mathcal D(A)=\{A-\operatorname{diag}(d):d\in[-1,1]^n\}.
$$

Call this family **regular** when every member is nonsingular. Only diagonal entries vary. This is precisely the entrywise interval matrix $[A-I_n,A+I_n]$.

<a id="av-01"></a>

## AV-01 — Recognizing the maximum finite number of solutions

[Open the problem folder](../../intervals-and-absolute-value-equations/AV-01/README.md) · [PDF](../../intervals-and-absolute-value-equations/AV-01/problem.pdf) · [LaTeX](../../intervals-and-absolute-value-equations/AV-01/problem.tex)


<a id="av-02"></a>

## AV-02 — Hardness of the spectral-norm condition number

[Open the problem folder](../../intervals-and-absolute-value-equations/AV-02/README.md) · [PDF](../../intervals-and-absolute-value-equations/AV-02/problem.pdf) · [LaTeX](../../intervals-and-absolute-value-equations/AV-02/problem.tex)


<a id="av-03"></a>

## AV-03 — Polynomial-time solution under the regularity promise

[Open the problem folder](../../intervals-and-absolute-value-equations/AV-03/README.md) · [PDF](../../intervals-and-absolute-value-equations/AV-03/problem.pdf) · [LaTeX](../../intervals-and-absolute-value-equations/AV-03/problem.tex)


## Uncounted source leads and cautions

- Hladík's [*Overconstrained and underconstrained systems of absolute value equations*](https://doi.org/10.1137/25M1744563), SIAM Journal on Matrix Analysis and Applications **47** (2026), 244–264, explicitly advertises open problems in its [author abstract](https://kam.mff.cuni.cz/~hladik/publ/b2hd-Hla2026a.html). The accessible author link leads to the publisher's restricted full text. Searches of the author's publication list, KAM-DIMATIA series, and arXiv did not provide the problem statements, so none are reconstructed or counted from the abstract.
- Older uniqueness and nonnegativity questions from Hladík's [2023 paper](https://arxiv.org/html/2209.06457v1), §3, are not admitted: Shweta Yadav and Dipti Dubey, [*On the properties of solution set of absolute value equations*](https://doi.org/10.1007/s11590-025-02255-9), Optimization Letters **20** (2026), 611–623, published online October 27, 2025, report addressing these questions. Only that paper's abstract was accessible, so the exact scope of the answers has not been verified.
- The survey's connectedness-complexity question is also held for further source checking. A finite orthant decomposition supplies a decision procedure, so merely requesting a characterization would not specify the unresolved algorithmic target adequately.
- The [2024 erratum](https://doi.org/10.1137/24M1635715) to Hladík's 2023 paper corrects a spectral-radius hypothesis in Proposition 3.5. That proposition is not used in the admitted statements.
