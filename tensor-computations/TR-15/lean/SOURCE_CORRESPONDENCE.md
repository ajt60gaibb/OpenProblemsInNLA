# TR-15 source correspondence

Reviewed repository revision: `8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`.
The canonical page and the complete mathematical manuscript were read before
the statement package was written. All files below remain unchanged.

| Repository source | SHA256 |
|---|---|
| `tensor-computations/TR-15/README.md` | `0969ca6e8492a50d85fde7fb031b2cb4cddb60c703a207d75498af44240632ed` |
| `tensor-computations/TR-15/problem.tex` | `d25295aa69ca4fff34c462cf4a5b0e51b305891d62bd62e8908c9dd9a70b64f1` |
| `tensor-computations/TR-15/problem.pdf` | `2b6717fce794fed2ebc02c3b5787645d02f90c76467b24d7754020d5d9514442` |
| `references/colbrook-unclaimed-2026-09-11/manuscripts/TR-15.md` | `31aaf87084303a6de0ef380270c973719efa027c6131c76b27a02cb489a1fa74` |
| `references/colbrook-unclaimed-2026-09-11/manuscripts/TR-15.tex` | `ca04bc1bc4847f283b74927e481ad2257618d1032a38963ea11bc1b17cb0a73c` |
| `references/colbrook-unclaimed-2026-09-11/manuscripts/TR-15.pdf` | `cfd74ef55129ed49c69444f613d08137c01b9fc129c84a437289bdc77357165a` |

The mathematical counterexample is Matthew J. Colbrook's *An exact
counterexample to odd-order Hankel H-eigenvalue inheritance*, dated
11 September 2026. Its [complete Markdown source](../../../references/colbrook-unclaimed-2026-09-11/manuscripts/TR-15.md)
and [canonical target](../README.md) are the retained sources of truth.
George Stepaniants's role is formalization, with the Department of Computing
and Mathematical Sciences, California Institute of Technology affiliation.
No transfer of mathematical authorship or priority claim is intended.

## Primary conventions

The [Ding–Qi–Wei author PDF](https://www.polyu.edu.hk/ama/staff/new/qilq/BIT-DQW.pdf)
was accessed on 12 September 2026. Its PDF pages 2–3 define multi-way arrays,
zero-based Hankel generators, and componentwise-power H-eigenpairs; page 8
also states the real eigenvalue and nonzero real vector convention explicitly.
The final Section 4 on PDF page 21 gives the inheritance conjecture and
identifies odd lower order as the unresolved case. Section 2.2 on PDF page 7
explains the dimension relation for a common generating vector. These agree
with the retained canonical statement and the present finite-array model.
[Journal DOI](https://doi.org/10.1007/s10543-016-0622-0).

The source distinguishes an associated positive-semidefinite Hankel matrix
from the absence of negative tensor H-eigenvalues. The present conjecture
uses only the latter premise. It does not add the stronger matrix hypothesis.

## Correspondence of definitions and exports

| Canonical or manuscript locator | Lean representation |
|---|---|
| Canonical Statement, orders and dimensions | `Admissible`, `lowerTensor`, `upperTensor`, `InheritanceConjecture`. All original natural-number parameters and the full real finite generating-vector quantifier are retained. |
| Canonical Statement, Hankel entries | `Tensor`, `generatorIndex`, `hankelTensor`; exact zero-based sum with a proved finite bound. |
| Canonical Statement, H-eigenvalue definition | `prependIndex`, `contraction`, `IsHEigenpair`; all ordered tuples, exactly `s−1` signed coordinate factors, and a nonzero real vector. |
| Canonical final implication | `HasNoNegativeHEigenvalues` and `InheritanceConjecture`; nonnegativity of every real H-eigenvalue is equivalent to absence of a negative one. |
| Manuscript Counterexample, data paragraph | `witnessGenerator`, `witnessLower`, `witnessUpper`, `witnessUpperVector`; no rounded coefficients or changed parameter. |
| Manuscript Counterexample proof, first contraction; Nonvacuity, remaining contractions | `lower_contractions`, for every real vector, not only the eventual eigenvector. |
| Manuscript Counterexample proof, positivity argument | `lower_eigenvalues_pos`, covering every real lower H-eigenpair. |
| Manuscript Counterexample proof, upper contraction and pair | `upper_contraction`, `upper_negative_eigenpair`. |
| Manuscript The premise is not vacuous | `rootPolynomial`, `lowerEigenvalue`, `lowerEigenvector`, `lower_eigenpair_exists`. The IVT root and eigenpair are conclusions. |
| Manuscript Proposition, full negative resolution | `counterexample`, `not_inheritanceConjecture`. |

The generic definitions also assign a value at order zero because Lean
functions are total. The original parameter restrictions exclude it and
exclude zero-dimensional tensors. For every admissible instance the tuple
length, exponent, and finite vector lengths coincide with the source.

## Computational and proof scope

The manuscript's tensor calculations and sum-of-squares argument are retained
exactly. The planned optimization uses the first slice for universal lower
positivity and the single surviving tuple for the upper pair; it changes no
quantifier or field. Mathlib's intermediate value theorem supplies the actual
root for the optional nonvacuity export, without numerical root isolation.

The source's remarks about other tensor inheritance theorems and submission
history are context, not formal hypotheses. The seven challenge exports cover
the full original target negation and the advertised numerical and nonvacuity
claims. They do not classify all odd-order tensors or prove a new result about
positive-semidefinite associated Hankel matrices.
