# MF-02 — Multiplication overhead of cubic sign compositions

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** open; explicit 2026 problem  
**Last checked:** 2026-09-08  

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
