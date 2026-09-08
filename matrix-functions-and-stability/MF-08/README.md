# MF-08 — NP-hardness of unrestricted static output-feedback stabilization

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Status:** open; longstanding complexity question, with related variants separated  
**Last checked:** 2026-09-08  

## Problem statement

Consider the decision language whose inputs are rational matrices
$A\in\mathbb Q^{n\times n}$, $B\in\mathbb Q^{n\times m}$, and
$C\in\mathbb Q^{p\times n}$, with positive dimensions included in the input.
The answer is yes precisely when there exists an unrestricted real matrix
$K\in\mathbb R^{m\times p}$ for which

$$
\operatorname{Re}\lambda<0\qquad\text{for every }\lambda\in\sigma(A+BKC).
$$

Is this language NP-hard under polynomial-time many-one reductions in the binary
encoding of the rational input? The requested output is a complexity theorem,
not another numerical heuristic for finding $K$.

## References and status evidence

Minyue Fu,
[Two Challenging Problems in Control Theory](https://www.eng.newcastle.edu.au/~mf140/home/Papers/Fu_UTSC.pdf),
§3, pp. 3–7, defines strict Hurwitz stabilization and distinguishes it from the
known NP-hard problem with entrywise bounds on $K$ (§3.1). Gillis and Sharma,
[Solving matrix nearness problems via Hamiltonian systems, matrix factorization, and optimization](https://arxiv.org/pdf/2202.02618),
§3.5.2, pp. 50–51 (2022 manuscript), reiterates the unresolved complexity of
static output feedback. Its broader stability convention should not replace the
strict inequality above. Follow-up searches for unrestricted stabilization
NP-hardness found no resolving reduction; claims about arbitrary bilinear matrix
inequalities or prescribed pole placement do not by themselves settle this
language. No claim of NP membership is made.
