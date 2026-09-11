# AA-01 — Deciding accurate evaluability of real polynomials

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Rating rationale:** Extreme because the existence of any accurate computation tree is a general decidability problem beyond checking a supplied algorithm; broad importance includes numerical stability, symbolic computation and automated algorithm design.  
**Status:** Solved
**Last checked:** 2026-09-11

<!-- colbrook-arithmetic -->
## Independently reviewed resolution - 2026-09-11

Theorem 1.1 gives an always-halting decision procedure for the exact constant-free finite-tree model in the statement. In every signed ordering chart $x_{\pi(i)}=\sigma_i(y_1+\cdots+y_i)$, the coefficientwise absolute majorant of $q(y)=p(x(y))$ must be bounded by $C|q(y)|$ on $y\geq0$. This finite real-quantifier criterion is necessary and sufficient; Sections 2-4 prove the equivalence and construct an evaluator when it holds. Both independent reviews cover comparisons, branching, stored-value reuse and arbitrary independent rounding errors.

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. [Complete manuscript](../../references/colbrook-arithmetic-2026-09-11/manuscripts/AA-01.pdf), [independent review](../../references/colbrook-arithmetic-2026-09-11/verification/reviews/AA-01-review.md), and [submission record](../../references/colbrook-arithmetic-2026-09-11/README.md). AI assistance is disclosed. Agent verification is not external human peer review or formal certification; no novelty or priority claim is made.

A [second independent proof review](../../references/colbrook-arithmetic-2026-09-11/verification/reviews/AA-01-second-review.md) also passes. The described experimental programs were not retained; their run counts and compiler/solver claims are not reproduced or certified here. The full mathematical proof, rather than those logs, supports the resolution. The ratings and rationale above are historical assessments of the original open target.

<!-- /colbrook-arithmetic -->

## Separate reviewed proof by George Stepaniants — 2026-09-11

**Affirmative resolution by George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology. The [complete manuscript](solution.tex) ([PDF](solution.pdf)), **Theorem 2.1 and Corollary 7.1**, gives an always-halting decision algorithm for exactly the constant-free finite-tree model below.

For each signed ordering of the input magnitudes, write the inputs in nonnegative gap coordinates and expand the transformed polynomial $q_T$. Accurate evaluability is equivalent to a uniform bound $W_T\le C_T|q_T|$, where $W_T$ is its coefficientwise absolute polynomial. The necessity proof couples actual executions, including error-dependent branches and stored values. A termwise evaluator proves sufficiency, including zeros and tied magnitudes. Finitely many real-quantifier-elimination tests decide the criterion and construct an evaluator on positive instances. No running-time bound or additional arithmetic primitive is assumed.

A separate Codex agent checked the full proof against the original target and returned **PASS** on 11 September 2026: [independent review](../../references/stepaniants-2026-09-11/verification/reviews/AA-01-review.md). The draft was developed in a ChatGPT conversation. Verification is independent automated-agent review, not external human peer review or formal proof certification. The original statement and earlier literature checks are retained; the ratings above are historical. [Authorship, source record and submission details](../../references/stepaniants-2026-09-11/README.md).

**Integration note — 2026-09-11.** This page retains both separately attributed, independently reviewed proofs. Stepaniants's [existing submission PR #68](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/68) was submitted while this exact target was open; Colbrook's [PR #89](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/89) has since been accepted into main. Both manuscripts and their review records are preserved, as requested by the maintainer. The mathematical statement below is unchanged.

## Problem statement

Consider finite arithmetic computation trees with exact real inputs
$x\in\mathbb R^n$. Arithmetic nodes use binary addition, subtraction, or
multiplication, each returning $(a\mathbin{\circ}b)(1+\delta_j)$.
Negation and comparisons ($<,=,>$) of available quantities are exact, and branching is
allowed. There are no constant input nodes. Each operation may have a different,
arbitrary error $\delta_j$; equal operands need not produce equal errors.
Previously computed values may be stored and reused. The tree describes
control flow, not a formula that recomputes each occurrence of a subexpression.

For $p\in\mathbb Z[x_1,\ldots,x_n]$ with $p(0)=0$, call such a tree $P$
accurate if $P(x,0)=p(x)$ and

$$
\forall\eta\in(0,1)\ \exists u\in(0,1)\quad
\forall x\in\mathbb R^n\ \forall\delta\in[-u,u]^{N(P)}:
\quad |P(x,\delta)-p(x)|\le\eta|p(x)|,
$$

where $N(P)$ numbers all rounded nodes; errors on unused branches are ignored.
The same tree must work for every $\eta$, and $u$ may depend on $p,P,\eta$
but not on $x$. The condition includes exact output at zeros of $p$.

### Question

Is there a Turing algorithm which, from the finite integer
coefficient list of any such $p$, always halts and decides whether an accurate
tree exists? No bound on the decision algorithm's running time is prescribed.

This is a basic obstruction to automatically constructing accurate algorithms
for determinants and other polynomial expressions associated with structured
matrices. Checking a supplied fixed tree is already decidable; deciding whether
any suitable tree exists is the question.

## References and status

J. Demmel, I. Dumitriu, O. Holtz, and P. Koev,
[*Accurate and Efficient Expression Evaluation and Linear Algebra*](https://people.eecs.berkeley.edu/~demmel/Demmel_pubs_07_11_final/B15_ActaNumerica08.pdf),
*Acta Numerica* 17 (2008), 87–145, Definitions 3.3–3.4, §3.3 and especially
§3.3.7. The finite-tree, integer-coefficient formulation fixes the traditional
real-arithmetic version of their decision question. Theorem 3.12 answers the
corresponding whole-space complex question, not the real one.
The original Demmel–Dumitriu–Holtz paper,
[*Toward accurate polynomial evaluation in rounded arithmetic*, v2](https://arxiv.org/pdf/math/0508350v2),
§§2.2–2.7, explicitly specifies uniformly bounded running time, exact comparisons,
and separate rounding errors, clarifying the computation-tree conventions.
Demmel's [21 October 2025 Simons seminar abstract](https://simons.berkeley.edu/events/when-accurate-efficient-expression-evaluation-linear-algebra-possible)
still identifies the broader accurate-evaluation decision procedure as open.
Searches on 2026-09-08 for accurate polynomial evaluability, real-arithmetic
decidability, and follow-ups to the cited authors found no complete decision
procedure or undecidability theorem for the displayed model. The recent talk
does not separately specify every tree convention used here.

## Earlier status check — 2026-09-10

Rechecked [Demmel et al., §3.3.7](https://people.eecs.berkeley.edu/~demmel/Demmel_pubs_07_11_final/B15_ActaNumerica08.pdf) and [Demmel’s October 2025 Simons abstract](https://simons.berkeley.edu/events/when-accurate-efficient-expression-evaluation-linear-algebra-possible), and searched for later real-polynomial decision procedures. The broad real accurate-evaluation question remains explicitly open in the seminar abstract; no complete algorithm or undecidability theorem for the displayed finite-tree model was located. The complex-domain characterization and fixed-tree verification do not answer this existence question.
