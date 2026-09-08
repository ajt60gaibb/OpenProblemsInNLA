# Absolute value equations and their conditioning

This chapter contains **3 admitted problems**. Ratings are editorial. Status checks were performed on **2026-09-08**; a bounded literature search cannot certify that a problem remains unsolved.

Absolute values and vector inequalities are componentwise. All algorithmic questions below use rational input in binary and the deterministic Turing model. Input length includes the matrix dimensions and the bit lengths of all rational coefficients.

For a real square matrix $A$, define the diagonal perturbation family

$$
\mathcal D(A)=\{A-\operatorname{diag}(d):d\in[-1,1]^n\}.
$$

Call this family **regular** when every member is nonsingular. Only diagonal entries vary. This is precisely the entrywise interval matrix $[A-I_n,A+I_n]$.

<a id="av-01"></a>

## AV-01 — Recognizing the maximum finite number of solutions

- **Difficulty:** challenging
- **Importance:** interesting to specialist
- **Status:** open; checked 2026-09-08
- **Area:** complexity of piecewise linear systems

For input $A\in\mathbb Q^{n\times n}$ and $b\in\mathbb Q^n$, $n\ge1$, set

$$
\Sigma_+(A,b)=\{x\in\mathbb R^n:Ax+|x|=b\}.
$$

**Problem.** Classify the computational complexity of deciding whether

$$
|\Sigma_+(A,b)|=2^n.
$$

In particular, is this decision problem in $\mathsf P$, or can an $\mathsf{NP}$-hardness or $\mathsf{coNP}$-hardness classification be established by polynomial-time many-one reductions? The task returns one Boolean answer. Infinite solution sets are negative instances. There is no promise that the solution set is finite.

**Reference.** Milan Hladík, [*Absolute value equations with $2^n$ solutions*](https://doi.org/10.1007/s11590-025-02251-z), Optimization Letters **20** (2026), 559–575, §2.3 and §7. The paper provides structural characterizations but explicitly leaves this recognition complexity open. Proposition 9 treats the subclass $\rho(|A|)<1$.

**Status evidence.** The version of record appeared October 6, 2025, in the April 2026 issue. Searches for the title with “complexity”, “solved”, and “2026”, and for “Hladík $2^n$ complexity”, found no subsequent classification. No separate arXiv version was located. The related result about more than $2^{n-1}$ solutions concerns a different threshold and does not settle this question.

<a id="av-02"></a>

## AV-02 — Hardness of the spectral-norm condition number

- **Difficulty:** challenging
- **Importance:** interesting to the community
- **Status:** open; checked 2026-09-08
- **Area:** condition estimation and rigorous error bounds

Let $n\ge1$ and let $A\in\mathbb Q^{n\times n}$ be promised to have regular $\mathcal D(A)$. Define

$$
c_2(A)=\max_{d\in[-1,1]^n}
\left\|(A-\operatorname{diag}(d))^{-1}\right\|_2
=\left(\min_{d\in[-1,1]^n}
\sigma_{\min}(A-\operatorname{diag}(d))\right)^{-1}.
$$

**Problem.** Is deciding $c_2(A)\ge t$, given such an $A$ and a positive rational threshold $t$, $\mathsf{NP}$-hard under polynomial-time Turing reductions that query only inputs satisfying the regularity promise?

This is a decision formulation of the published hardness conjecture. Equality belongs to the yes case. Checking the promise is outside the task. The spectral norm is the operator norm induced by the Euclidean vector norm.

**References.** Moslem Zamani and Milan Hladík, [*Error bounds and a condition number for the absolute value equations*](https://doi.org/10.1007/s10107-021-01756-6), Mathematical Programming **198** (2023), 85–113, §2, paragraph before Proposition 3; §2.1 and §7. The maximum is attained at a sign vector by Proposition 2; Proposition 6 gives a formula for symmetric $A$. The conjecture concerns general matrices.

The quantity bounds forward error by residual for $Ax-|x|=b$; see Theorem 7. Its computation remains explicitly unclassified in Hladík et al.'s [2026 survey](https://doi.org/10.1007/s10589-025-00717-5), §5.4.

**Status evidence.** The original paper's latest arXiv version is [v2, January 17, 2020](https://arxiv.org/abs/1912.12904); the journal text was published January 30, 2022. Searches for “absolute value equations condition number 2026”, “spectral norm complexity”, and “2-norm NP-hard” found no resolution.

<a id="av-03"></a>

## AV-03 — Polynomial-time solution under the regularity promise

- **Difficulty:** extreme
- **Importance:** broadly interesting
- **Status:** open; checked 2026-09-08
- **Area:** algorithms for piecewise linear systems and complementarity

**Problem.** Is there a deterministic algorithm and a polynomial $p$ such that, for every $n\ge1$, rational $A\in\mathbb Q^{n\times n}$ and $b\in\mathbb Q^n$ with regular $\mathcal D(A)$, the algorithm outputs the exact rational vector $x$ satisfying

$$
Ax-|x|=b
$$

within $p(\ell)$ bit operations, where $\ell$ is the binary input length?

The promise guarantees existence and uniqueness. No certificate of regularity is supplied or required, and behavior on inputs violating the promise is unrestricted. Polynomial dependence on coefficient bit length is allowed; this does not ask for a strongly polynomial algorithm.

**References.** Milan Hladík, Hossein Moosaei, Fakhrodin Hashemi, Saeed Ketabchi, and Panos M. Pardalos, [*An overview of absolute value equations: from theory to solution methods and challenges*](https://doi.org/10.1007/s10589-025-00717-5), Computational Optimization and Applications **93** (2026), 435–488, §2.4.2, paragraph following conditions (15)–(16); §2.2 gives the complementarity connection.

This is the AVE formulation of the polynomial-time P-matrix linear complementarity problem; it is counted once. Michaela Borzechowski, John Fearnley, Spencer Gordon, Rahul Savani, Patrick Schnider, and Simon Weber, [*Two Choices Are Enough for P-LCPs, USOs, and Colorful Tangents*](https://doi.org/10.4230/LIPIcs.ICALP.2024.32), ICALP 2024, §1, explicitly retain that algorithmic question.

**Status evidence.** The survey appeared online August 8, 2025. Borzechowski et al.'s latest [arXiv version](https://arxiv.org/abs/2402.07683) is v2, May 21, 2024. Searches for “P-matrix linear complementarity 2026 polynomial-time” and “P-LCP solved polynomial algorithm” found no solution. E.-Nagy and Végh's [June 30, 2026 revision](https://arxiv.org/html/2605.10701v2), abstract and §6, gives an algorithm whose complexity also depends on an optimized handicap number; it does not give the required polynomial bound in input length alone.

## Uncounted source leads and cautions

- Hladík's [*Overconstrained and underconstrained systems of absolute value equations*](https://doi.org/10.1137/25M1744563), SIAM Journal on Matrix Analysis and Applications **47** (2026), 244–264, explicitly advertises open problems in its [author abstract](https://kam.mff.cuni.cz/~hladik/publ/b2hd-Hla2026a.html). The accessible author link leads to the publisher's restricted full text. Searches of the author's publication list, KAM-DIMATIA series, and arXiv did not provide the problem statements, so none are reconstructed or counted from the abstract.
- Older uniqueness and nonnegativity questions from Hladík's [2023 paper](https://arxiv.org/html/2209.06457v1), §3, are not admitted: Shweta Yadav and Dipti Dubey, [*On the properties of solution set of absolute value equations*](https://doi.org/10.1007/s11590-025-02255-9), Optimization Letters **20** (2026), 611–623, published online October 27, 2025, report addressing these questions. Only that paper's abstract was accessible, so the exact scope of the answers has not been verified.
- The survey's connectedness-complexity question is also held for further source checking. A finite orthant decomposition supplies a decision procedure, so merely requesting a characterization would not specify the unresolved algorithmic target adequately.
- The [2024 erratum](https://doi.org/10.1137/24M1635715) to Hladík's 2023 paper corrects a spectral-radius hypothesis in Proposition 3.5. That proposition is not used in the admitted statements.
