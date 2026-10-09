# MF-08 — NP-hardness of unrestricted static output-feedback stabilization

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Historical rating rationale:** Extreme because this is a longstanding complexity barrier for unrestricted feedback design; broad impact connects control synthesis, optimization, and computational complexity.  
**Status:** Solved  
**Last checked:** 2026-09-18  

## Resolution — 18 September 2026

**Affirmative resolution.** Unrestricted static output-feedback stabilization
is NP-hard. Johan Löfberg proves this for integer single-input plants in
[Theorem 1.1 of arXiv:2609.16886v1](https://arxiv.org/html/2609.16886v1).
Amir Ali Ahmadi, Abraar Chaudhry, Ijay Narang and Yukai Tang prove strong
NP-hardness for integer single-output plants in
[Theorem 1 of arXiv:2609.20636v1](https://arxiv.org/html/2609.20636v1).

Each integer subclass is contained in the original rational-input language:
encode integers with denominator one, retaining the same unrestricted real
gain and the strict Hurwitz condition. Composing this inclusion with either
paper's polynomial-time many-one reduction settles the retained question.
The theorem credit belongs to the cited authors.

**Review level.** These are v1 preprints submitted on 15 and 17 September 2026.
A separate Codex-agent review examined both complete continuous-time arguments
and their match to this problem; no substantive gap was found. This is informal
review, with no claim of journal acceptance, external human peer review or Lean
verification. [Reference note and review scope](../../references/stepaniants-mf08-2026-09-18/README.md).

**Literature application and curation:** George Stepaniants, Department of
Computing and Mathematical Sciences, California Institute of Technology.
The difficulty and importance ratings above are historical. The original
statement and the 10 September audit are retained.

## Problem statement

Consider the decision language whose inputs are rational matrices
$`A\in\mathbb Q^{n\times n}`$, $`B\in\mathbb Q^{n\times m}`$, and
$`C\in\mathbb Q^{p\times n}`$, with positive dimensions included in the input.
The answer is yes precisely when there exists an unrestricted real matrix
$`K\in\mathbb R^{m\times p}`$ for which

```math
\mathop{\mathrm{Re}}\nolimits\lambda<0\qquad\text{for every }\lambda\in\sigma(A+BKC).
```

Is this language NP-hard under polynomial-time many-one reductions in the binary
encoding of the rational input? The requested output is a complexity theorem,
not another numerical heuristic for finding $`K`$.

## References and status evidence

Minyue Fu,
[Two Challenging Problems in Control Theory](https://www.eng.newcastle.edu.au/~mf140/home/Papers/Fu_UTSC.pdf),
§3, pp. 3–7, defines strict Hurwitz stabilization and distinguishes it from the
known NP-hard problem with entrywise bounds on $`K`$ (§3.1). Gillis and Sharma,
[Solving matrix nearness problems via Hamiltonian systems, matrix factorization, and optimization](https://arxiv.org/pdf/2202.02618),
§3.5.2, pp. 50–51 (2022 manuscript), reiterates the unresolved complexity of
static output feedback. Its broader stability convention should not replace the
strict inequality above. Follow-up searches for unrestricted stabilization
NP-hardness found no resolving reduction; claims about arbitrary bilinear matrix
inequalities or prescribed pole placement do not by themselves settle this
language. No claim of NP membership is made.

## Audit — 2026-09-10

Rechecked [Fu, §3.1](https://www.eng.newcastle.edu.au/~mf140/home/Papers/Fu_UTSC.pdf) and [Gillis–Sharma, §3.5.2](https://arxiv.org/pdf/2202.02618). Searches for unrestricted static-output-feedback NP-hardness found no applicable reduction. Bounded feedback gains, prescribed poles, and general bilinear inequalities remain different decision problems; later generic hardness descriptions do not establish this one.
