# IV-06 — Number of components of a real interval eigenvalue set

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Lean verified
**Last checked:** 2026-09-12

**Rating rationale:** Controlling the topology of the real spectrum for nonsymmetric uncertain matrices appears to require new analysis, warranting challenging. The component-count bound primarily advances specialist interval spectral enclosure theory.

**Area:** interval linear algebra; eigenvalue computation  

<!-- colbrook-intervals -->
## Independently reviewed resolution - 2026-09-11

**Negative resolution.** Theorem 1 gives a $`3\times3`$ independent-entry interval matrix with at least four components in its real eigenvalue set. Four exact integer eigenpairs at $`-3,0,3,25`$ and excluded separators $`-1,1,12`$ refute the universal at-most-$`n`$ conjecture. No symmetry assumption is introduced, and locating every component endpoint is unnecessary.

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. See the [complete manuscript](../../references/colbrook-intervals-2026-09-11/manuscripts/IV-06.pdf), [independent agent review](../../references/colbrook-intervals-2026-09-11/verification/reviews/IV-06-review.md) and [submission record](../../references/colbrook-intervals-2026-09-11/README.md). The source archive identifies the drafts as AI-generated; authorship is recorded at the submitter's request. That original agent review was informal; the later Lean verification is documented below. External human peer review is not claimed.

The difficulty, importance and rating rationale below are historical assessments of the original open target. The original statement and dated audits are preserved.
<!-- /colbrook-intervals -->

## Lean proof and verification evidence - 2026-09-12

**The complete original component-bound conjecture is Lean verified with a negative answer.** The [proof at revision 18b5ef3](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/18b5ef3127da0ae4f68e09289f60fd4f6e3d9bcb/intervals-and-absolute-value-equations/IV-06/lean) proves that the unchanged dimension-three source box has at least four actual connected components. It retains the full independent-entry interval family, genuine nonzero real eigenvectors and the topology of the attained real-eigenvalue subset. Component cardinality is the actual `Cardinal` of `ConnectedComponents`; no finiteness, symmetry or all-real-spectrum assumption is added.

**Lean formalization:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. **Matthew J. Colbrook** retains authorship of the mathematical counterexample. Milan Hladík, David Daney and Elias P. Tsigaridas retain the original question and background credit.

The eight [checked exports](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/18b5ef3127da0ae4f68e09289f60fd4f6e3d9bcb/intervals-and-absolute-value-equations/IV-06/lean/Solution.lean), each with prefix `NLA.IV06.`, are:

- `eigenvalue_determinant_semantics`: genuine eigenvector and characteristic-determinant equivalence for every real square matrix.
- `family_and_determinant_semantics`: equality with the complete endpoint box and the actual determinant polynomial.
- `witness_eigenpairs`: four admissible matrices and their nonzero eigenvectors at $`-3,0,3,25`$.
- `witness_separators`: determinant bounds for every box member, excluding $`-1,1,12`$.
- `connected_component_intervals`: actual equal component classes force interval containment for any real subset.
- `four_components`: an injective map from four representatives into the genuine component quotient.
- `counterexample`: admissible endpoints whose component cardinality strictly exceeds dimension three.
- `not_componentBoundConjecture`: negation of the complete original universal claim.

Two independent statement approvals preceded implementation; two independent final proof referees approved the frozen proof after fresh source elaboration and actual-term checks. [Ubuntu run 34725713519](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34725713519) matched all eight exports with the sandboxed Comparator, replayed the solution in Lean's default kernel and passed both actual isolation/rejection-control suites. The [operational audit and original artifacts](lean/verification/linux-2026-09-12/) bind all 200 candidate inputs; the [separate root acceptance](lean/verification/root-operational-2026-09-12/ROOT-CHECKS.json) independently checked their identity and actual execution. All 17 internal/public transitive axiom reports allow only `propext`, `Classical.choice` and `Quot.sound`. Operational and publication work does not add mathematical referees. External human peer review is not claimed.

The pins are **Lean 4.33.1**, [LeanCert 621a43d](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926) and [Mathlib 0df444a](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474). A material explicit kernel LeanCert certificate proves $`-18<0`$ on a singleton; exact algebra and universal affine bounds reduce every separator to this sign. Genuine connectedness and cardinality complete the argument. No eigenvalue approximation, root isolation or interval subdivision is used. Exactly four components, complete endpoints and a replacement bound for all dimensions are outside these exports. See the [project guide](lean/README.md), [manifest](lean/formalization.yaml), [reviews](lean/reviews/) and [dependency pins](lean/lake-manifest.json).

From the immutable verified revision on a documented [non-root Linux host](../../tools/lean/HARNESS.md), reproduce with:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  intervals-and-absolute-value-equations/IV-06/lean \
  /absolute/path/to/nla-lean-tools
```

## Problem statement

For every integer $`n\ge1`$ and real matrices $`L,U\in\mathbb R^{n\times n}`$ with $`L\le U`$ entrywise, form the interval matrix family

```math
\mathcal A=\{A\in\mathbb R^{n\times n}:L\le A\le U\}.
```

Each entry varies independently in its prescribed closed interval; singleton intervals are allowed. Define the set of all real eigenvalues attained by the family by

```math
\Lambda_{\mathbb R}(\mathcal A)
=\{\lambda\in\mathbb R:\exists A\in\mathcal A,\ \exists x\in\mathbb R^n\setminus\{0\},\ Ax=\lambda x\}.
```

Must $`\Lambda_{\mathbb R}(\mathcal A)`$ have at most $`n`$ connected components? Equivalently, must there exist $`0\le m\le n`$ and real numbers $`a_r\le b_r`$, $`1\le r\le m`$, such that

```math
\Lambda_{\mathbb R}(\mathcal A)=\bigcup_{r=1}^{m}[a_r,b_r]?
```

The empty set corresponds to $`m=0`$, and a singleton eigenvalue component counts as one interval. No symmetry, diagonalizability, or reality of the entire spectrum is assumed. Only real eigenvalues contribute to the set.

Interval eigensolvers enclose all eigenvalues allowed by uncertain matrix entries. The conjecture bounds the number of separated real spectral regions they must represent, without claiming that their endpoints can be found efficiently. Finiteness and compactness of the union are known; the proposed linear bound is the unresolved claim. For families restricted to symmetric matrices, the ordered eigenvalue functions already give $`n`$ compact intervals, as explained in the second reference; that does not address the family above.

## References

Milan Hladík, David Daney, and Elias P. Tsigaridas, [*An algorithm for addressing the real interval eigenvalue problem*](https://doi.org/10.1016/j.cam.2010.11.022), Journal of Computational and Applied Mathematics **235** (2011), 2715–2730, §1, p. 2716, paragraph immediately after the definition of $`\Lambda`$.

The same authors, [*Characterizing and approximating eigenvalue sets of symmetric interval matrices*](https://www-sop.inria.fr/coprin/PDF/CAMWA6430.pdf), Computers & Mathematics with Applications **62** (2011), 3152–3163, §2, p. 3153; [DOI](https://doi.org/10.1016/j.camwa.2011.08.028).

## Status check

On 2026-09-10, checked the published formulation, the authors' follow-up on symmetric interval matrices, Hladík's current publication record, and searches for the original title, interval eigenvalue components, the at-most-$`n`$ claim, and 2025/2026 developments. No primary source proving or refuting the general conjecture was located. This is a bounded literature check; papers addressing only symmetric interval families do not settle the stated question.

## Independent audit — 2026-09-10

The primary 2011 JCAM text explicitly poses the at-most-$`n`$ conjecture for independent entries. The full symmetric follow-up instead studies the coupled family $`\mathcal A^S=\{A\in\mathcal A:A=A^T\}`$, generally a proper subset, as its §2 explains. Its result alone does not justify the previous partial-resolution label for the displayed independent-entry target. Targeted later component-count and exact-conjecture searches found no proof or counterexample; the explicit openness statement is historical.
