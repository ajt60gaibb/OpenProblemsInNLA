---
title: "RA-20: A counterexample to the symmetric rank-two critical-point formula"
author: Codex automated maintainer audit
affiliation: OpenProblemsInNLA repository audit
date: 11 September 2026
review-footer: "Independently checked by automated agents; not external human peer review."
---

## Proposition

Under the precise full-Frobenius, complex-bilinear, smooth-locus definition in [RA-20](README.md), one has $e_{3,3}=3$. The displayed conjecture predicts $27(3-3)+4=4$, so its universal assertion is false.

## Proof

Every hollow symmetric complex $3\times3$ matrix has the form

$$
X(a,b,c)=\begin{pmatrix}0&a&b\\a&0&c\\b&c&0\end{pmatrix},
\qquad \det X(a,b,c)=2abc.
$$

Thus $W_{3,3}$ is the reduced hypersurface $abc=0$ in $\mathbb C^3$, the union of the three coordinate planes. Its gradient is $(bc,ac,ab)$. Consequently its smooth locus consists exactly of points with one zero coordinate and two nonzero coordinates. Points in intersections of the planes are singular and are excluded, even when their matrix rank is two.

For symmetric data $U$, write $\alpha=u_{12}$, $\beta=u_{13}$, and $\gamma=u_{23}$. The full-Frobenius objective restricted to hollow matrices is

$$
d_U(X)=\sum_{i=1}^3u_{ii}^2+
2\bigl((a-\alpha)^2+(b-\beta)^2+(c-\gamma)^2\bigr).
$$

Take $\alpha\beta\gamma\ne0$. This condition defines a nonempty Zariski-open set of data; diagonal entries are arbitrary. On the smooth part of $a=0$, tangent derivatives with respect to $b,c$ vanish exactly at $(0,\beta,\gamma)$. It is a smooth point because $\beta\gamma\ne0$. The other two components give exactly $(\alpha,0,\gamma)$ and $(\alpha,\beta,0)$. These three points are distinct and exhaust the smooth locus's critical points, since every smooth point belongs to exactly one component.

Each restricted Hessian is $4I_2$, so each critical point is nondegenerate and has multiplicity one. The number of generic complex critical points is therefore

$$e_{3,3}=1+1+1=3\ne4.$$

This proves the proposition and refutes the original universal target. $\square$

## Source and scope

Kubjas, Sodomaco and Tsigaridas, [*Exact solutions in low-rank approximation with zeros*, arXiv:2010.15636v2](https://arxiv.org/pdf/2010.15636v2), printed p.21, Conjecture 5.6 and Table 7, give the value four for this symmetric rank-at-most-two case. The argument above uses precisely the full Frobenius metric stated in RA-20. It does not diagnose the source computation, establish a corrected all-order formula, or settle the other formulas separately.

The counterexample was identified and independently reconstructed by Codex agents during the maintainer audit. [Audit and reproducible exact checks](../../references/research-expansion-2026-09-11/ra20-resolution/README.md) document that review. No external human peer review, formal certification, or historical-priority determination is claimed.
