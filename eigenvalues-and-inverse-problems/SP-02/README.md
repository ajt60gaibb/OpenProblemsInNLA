# SP-02 — The sharp off-diagonal threshold for spectral-subspace rotation

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Open  
**Last checked:** 2026-09-10  

**Rating rationale:** Challenging reflects an optimal off-diagonal perturbation bound for arbitrary separated spectral sets; community impact is a sharp guarantee for invariant-subspace stability.

Let $A$ be a self-adjoint, possibly unbounded operator on a separable complex Hilbert space, with $\sigma(A)=\sigma\cup\Sigma$ for nonempty closed sets satisfying $d=\operatorname{dist}(\sigma,\Sigma)>0$. Let $P=E_A(\sigma)$. Suppose a bounded self-adjoint perturbation $V$ is off-diagonal relative to this decomposition:
$$
PVP=0,\qquad (I-P)V(I-P)=0.
$$
Writing $O_r(S)=\{x\in\mathbb R:\operatorname{dist}(x,S)<r\}$ and $Q=E_{A+V}(O_{d/2}(\sigma))$, does
$$
\|V\|<\frac{\sqrt3}{2}d\quad\Longrightarrow\quad\|P-Q\|<1
$$
hold universally? Here $E_B$ is the spectral projection measure of $B$, and norms are operator norms. No ordering of the two spectral sets is assumed.

The source retains the full operator setting, encompassing Hermitian block matrices in invariant-subspace computations. The threshold $\sqrt3/2$ already guarantees that the perturbed spectral components stay separated; the unresolved assertion controls their maximal subspace angle. Off-diagonal structure makes this a different threshold problem from the general-perturbation constant $1/2$.

## References

 A. Seelmann, *Notes on the subspace perturbation problem for off-diagonal perturbations*, Proceedings AMS 144 (2016), 3825–3832, §1, (1.1)–(1.4), and Theorem 2.5 ([primary manuscript](https://arxiv.org/pdf/1412.6294); [journal](https://doi.org/10.1090/proc/13118)). A. Seelmann, *Unifying the treatment of indefinite and semidefinite perturbations in the subspace perturbation problem*, Operators and Matrices 15 (2021), 1181–1188 ([primary paper](https://files.ele-math.com/articles/oam-15-74.pdf)), treats a different extension of the perturbation hypotheses.

## Status check — 2026-09-08

 The 2016 paper explicitly conjectures $c_{\mathrm{opt-off}}=\sqrt3/2$ and proves $c_{\mathrm{opt-off}}>0.6940725$. The 2021 extension does not attain this off-diagonal endpoint. Searches for “off-diagonal subspace perturbation”, “0.6940725”, “sqrt 3”, “optimal constant”, “conjecture”, and 2024–2026 found no resolution. This is a historical-source entry with a bounded later-literature check, not a certified claim of present openness.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

## Audit update — 2026-09-10

Rechecked [Seelmann's account](https://arxiv.org/pdf/1412.6294) and the [2021 follow-up](https://files.ele-math.com/articles/oam-15-74.pdf). The proved sufficient constant above 0.694 remains below the conjectured threshold $\sqrt3/2$. Searches for subsequent off-diagonal optimal-threshold results found no general proof or counterexample. A smaller sufficient constant is progress but not a proved subfamily of the optimal-constant determination.
