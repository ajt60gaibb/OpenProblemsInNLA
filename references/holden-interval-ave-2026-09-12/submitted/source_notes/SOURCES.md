# Canonical statements and external dependencies

All sources below were consulted on 2026-09-12. Repository identifiers are
**Git blob SHAs for the individual files**, not a repository commit SHA.
No repository status or file was changed.

| Source | Identifier / URL | Use |
|---|---|---|
| Category README | https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/intervals-and-absolute-value-equations/README.md ; blob `9315aeeaefa0e2bcd3a441c4fa6ae1280e4c4037` | Two remaining targets and requested ordering. |
| AV-03 canonical README | https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/intervals-and-absolute-value-equations/AV-03/README.md ; blob `7f68574d70d282abedb27d00315db95ab1436324` | Exact rational binary-input promise problem and current target scope. |
| IV-01 canonical README | https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/intervals-and-absolute-value-equations/IV-01/README.md ; blob `4317a0f6303eebaf3894a31b992411540bb47533` | Arbitrary real dimension n>=5, checker endpoints, common signature, zero minors, nonsingularity. |
| Mohammad Adm and Jürgen Garloff, *Certification of the Sign Regularity of Matrix Intervals*, Acta Scientiarum Mathematicarum, published 2026-01-17 | https://link.springer.com/article/10.1007/s44146-026-00223-y | Primary external mathematical input: Theorem 3.3, same-parity fixed-entry interval theorem. Theorem 3.2 distinguishes the strict case. The signature discussion supplies the comparison for the n=5 example. |
| E.-Nagy and Végh, *Handicap reduction for linear complementarity problems*, arXiv:2605.10701v2, 2026-06-30 | https://arxiv.org/html/2605.10701v2 | Definition and role of the optimized handicap. The exact cyclic-family formula in this pack is proved independently. |

The elementary determinant, Cramer, secant, continuity, weighted-norm,
Neumann-series, and graph-potential arguments used in the new proof candidates
are given in the pack rather than attributed to an unverified external theorem.
The P-LCP equivalence is included as an audited known reduction, not a novelty
claim. No claimed theorem depends on a floating-point numerical experiment.

## Queue

AV-03 was the only `open` target, rated extreme. IV-01 was the only partially
resolved target, rated challenging. Therefore the status-first requested
ordering is AV-03 followed by IV-01, despite the latter's lower difficulty.
The retained solved entries AV-01, AV-02, and IV-02 through IV-06 were outside
the open count and were not treated as remaining research targets.

## Literature limitation

The source review verifies the targets and the explicit theorem dependency.
It does not certify that the structured algorithms, graph criterion, SCC
normal form, or exact cyclic handicap formula are historically unpublished.
Independent priority checking is recommended before a novelty claim or submission.

A final priority-oriented check also found Choudhury, Kannan, and Khare,
*Sign non-reversal property for totally non-negative and totally positive
matrices, and testing total positivity of their interval hull*, arXiv:2007.09999
(https://arxiv.org/abs/2007.09999). Its abstract explicitly reports a two-element
interval test for strict total positivity of order k and a finite test for the
weak version. This reinforces the need to distinguish already known strict
subclasses from the new proof candidates involving endpoint zero minors.
The present proofs do not rely on a theorem from that paper; historical
priority of the stated weak-boundary refinements still requires review.
