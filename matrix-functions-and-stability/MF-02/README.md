# MF-02 — Multiplication overhead of cubic sign compositions

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because optimal cubic compositions must be compared with unrestricted evaluation programs; community impact comes from reusable matrix-sign iterations.  
**Status:** Solved  
**Last checked:** 2026-09-12  

## Resolution - uniform constant-factor asymptotic order

**Resolution recorded 2026-09-12.** The canonical asymptotic-order target is settled:

$$T_{\min}(m,\delta)=\Theta(m+1)\qquad(0<\delta<1),$$

with absolute constants uniform in the gap, including gaps depending on the multiplication budget. The [Theorem in Section 1 and proof in Sections 2-5](solution.md) give the explicit bounds

$$\left\lfloor\frac m2\right\rfloor\le T_{\min}(m,\delta)\le m\quad(m\ge2),
\qquad T_{\min}(0,\delta)=T_{\min}(1,\delta)=1.$$

**Expository proof-note author:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. [Proof PDF](solution.pdf) · [Standalone TeX](solution.tex).

**Prior work and exact scope.** Cheon, Kim and Kim's [ASIACRYPT 2020 work](https://doi.org/10.1007/978-3-030-64834-3_8), especially Lemma 3 and its constant-factor complexity analysis, already yields uniform constant-factor order by combination with the classical degree bound. The optimized cubic is the earlier [Chen-Chow construction, equations (3.3)-(3.6)](https://www.mcs.anl.gov/papers/P5059-0114.pdf), also discussed in [Polar Express, Appendix F](https://arxiv.org/html/2505.16932v5). The present self-contained note supplies the explicit comparison $T_{\min}\le m$; it claims neither a new cubic iteration nor first discovery of constant-factor optimality. The exact smallest stage count, the optimal leading constant, and the stronger source question comparing the errors at the same multiplication budget remain unanswered.

**Verification.** A separate [independent Codex-agent mathematical and scope review](../../references/stepaniants-mf02-2026-09-12/verification/independent-review/MF-02-independent-review.md) returned PASS for the theorem and the literal canonical asymptotic-order target. A second [independent source and attribution review](../../references/stepaniants-mf02-2026-09-12/verification/source-review/REVIEW.md) confirms the scope and prior-work distinctions. The [submission record](../../references/stepaniants-mf02-2026-09-12/README.md) preserves both reviews, the original candidate and exact checks. Substantial AI assistance is disclosed. This is informal automated-agent review, not external human peer review or formal verification. No novelty or priority certification is asserted.

The original target, permanent ID, references and dated history remain below. The displayed ratings are retained as historical ratings of that target.

## Context and notation

For $m\in\mathbb N_0$ and $0<\delta<1$, put

$$
I_\delta=[-1,-\delta]\cup[\delta,1].
$$

Let $\mathcal P_m$ consist of real polynomials computed from $1,x$ by
straight-line programs using at most $m$ nonscalar multiplications; real linear
combinations cost nothing. Define

$$
E_m(\delta)=\inf_{p\in\mathcal P_m}
\max_{x\in I_\delta}|p(x)-\operatorname{sign}(x)|.
$$

The arithmetic model concerns a single polynomial identity valid for matrices of every size.

## Problem statement

Define

$$
C_T(\delta)=\inf_{a_t,b_t\in\mathbb R}
\max_{x\in I_\delta}|(q_T\circ\cdots\circ q_1)(x)-\operatorname{sign}(x)|,
\qquad q_t(x)=a_tx+b_tx^3.
$$

Determine the asymptotic dependence on $m,\delta$ of

$$
T_{\min}(m,\delta)=\inf\{T\in\mathbb N_0:C_T(\delta)\le E_m(\delta)\},
$$

where the empty composition is $x$ and $\inf\varnothing=+\infty$.
Each stage costs at most two matrix products.

## References and status evidence

Amsel et al.,
[Simons workshop report](https://arxiv.org/html/2602.05394v3), §6.3, Problem 6.5.
Rubensson, Jarlebring and Lorentzon,
[degree-eight recursive expansion](https://arxiv.org/html/2606.24701v1), §7,
provides a June 2026 follow-up discussion; it does not settle this comparison.

## Scope

[MF-01](../MF-01/README.md) asks for an optimum value over general evaluation programs.
This problem measures the price of a particular, reusable composition architecture;
the two tasks are related but have different requested outputs.

## Audit — 2026-09-10

Rechecked [Problem 6.5](https://arxiv.org/html/2602.05394v3#S6.SS3) and the [degree-eight paper's concluding discussion](https://arxiv.org/html/2606.24701v1). The optimal composition comparison remains posed. Searches for cubic and recursive sign-expansion improvements found no resolution of this exact multiplication-overhead target.
