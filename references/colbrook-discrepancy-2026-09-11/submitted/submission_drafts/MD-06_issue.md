# [MD-06] Negative-resolution proof claim for random cubic-graph synchronization

### Affected entry

MD-06, **Global synchronization of a random cubic graph**. The affected claim is the proposed limit one for the probability that every local minimum of the homogeneous attractive Kuramoto energy is synchronized.

### Correction or result

**Proposed status: Solution claimed. Independent mathematical review is requested.**

The attached manuscript, *Random cubic graphs admit nonsynchronized stable Kuramoto equilibria*, claims the opposite limit:

\[
\lim_{\substack{n\to\infty\\ n\ \mathrm{even}}}
\Pr\!\left(\text{every local minimum of }E_{G_n}\text{ is synchronized}\right)=0.
\]

This covers the full displayed target, not just a finite family of counterexamples. The model is exactly the uniform distribution on labelled simple 3-regular graphs on an even number of vertices. The energy is the sum over unordered edges of `1-cos(theta_i-theta_j)`, with phases on the full product torus. The constructed minima are strict modulo common rotation, hence are local minima in the sense required by the entry.

The original question and ID should remain visible. A move to **Solved** is not requested before the proof receives independent review.

### Evidence

**Primary proof claim attached:** `md06_counterexample.pdf`, with editable LaTeX source and exact verification programs in the accompanying package. The main statement is Theorem 1. Sections 2–4 contain the analytic proof. Section 5 contains supplementary exact finite checks; those checks are not used to infer the asymptotic probability limit.

The proof has the following structure. For each radius `R>=4`, the scalar equation

\[
3\arcsin t_R+2\sum_{j=1}^{R-1}\arcsin(t_R/2^j)=2\pi
\]

has a unique root in `(0,1)`. On a cycle of length divisible by four, assign signs `++--` repeatedly, and extend a decaying arcsine profile down the outward binary trees. A clean radius-`R` neighborhood gives exact force cancellation except at its boundary. All edge cosines have a fixed positive lower bound, while the squared boundary gradient is `ell*t_R^2*2^(1-R)`. A compact-ball argument using the graph Laplacian gap yields a nearby exact nonsynchronized local minimum, despite arbitrary exterior connections.

For each fixed multiple of four `ell`, a fixed sufficiently large radius works. The random-graph inputs then give

\[
\limsup_n\Pr(\text{global synchronization})
\le \exp\!\left(-\frac{2^\ell}{2\ell}\right).
\]

Letting `ell` tend to infinity only after taking the limit superior proves the claimed zero limit. No independence of the spectral event and cycle counts is assumed.

**Established inputs, with exact locators:**

1. Charles Bordenave, *A new proof of Friedman's second eigenvalue theorem and its extension to random lifts*, [arXiv:1502.04482](https://arxiv.org/abs/1502.04482), Theorem 1 and the labelled simple-graph model, printed page 2. For cubic graphs this gives `lambda_2(L)>=1/10` with probability tending to one.
2. Tobias Johnson, *Exchangeable pairs, switchings, and random regular graphs*, [arXiv:1112.0704v5](https://arxiv.org/abs/1112.0704v5), Theorem 11, printed page 12, for the fixed-cycle Poisson law; Section 2 and Proposition 1(a), printed page 3, for the simple-graph model and the fixed-subgraph estimate used to exclude dirty fixed neighborhoods.
3. The target conjecture is Definition 2.1 and Conjecture 3, printed page 3, of [arXiv:2504.20539v1](https://arxiv.org/abs/2504.20539v1).

**Prior related work:** DeVille and Ermentrout, *Phase-locked patterns of the Kuramoto model on 3-regular graphs*, Chaos 26 (2016), 094820, [DOI 10.1063/1.4961064](https://doi.org/10.1063/1.4961064), [arXiv:1512.06140](https://arxiv.org/abs/1512.06140). Their finite constructions and the numerical trend discussed in Section IV are acknowledged; no priority claim is made for those observations.

The manuscript and programs are AI-assisted work. The finite arithmetic checks pass, but the asymptotic proof has not received external peer review or proof-assistant formalization. The full argument is supplied so that the claim can be evaluated directly; passing a numerical or finite verification script alone is not offered as evidence of an established major resolution.

### Rating implications, if any

No change to the historical difficulty or importance labels is requested at the claim stage. After review, the original ratings may be retained as historical metadata. The exact surviving mathematical status should follow the outcome of that review.
