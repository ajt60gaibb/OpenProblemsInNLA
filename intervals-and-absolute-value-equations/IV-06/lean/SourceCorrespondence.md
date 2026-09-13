# IV-06: original target and complete proof correspondence

Source base: `f41f1f9ffa2171550d4bb795862c6170c4f26070`, the observed upstream `main` on 12 September 2026. The permanent canonical path is `intervals-and-absolute-value-equations/IV-06/README.md`. All eight source files in [source-inputs.json](source-inputs.json) were read in full and match their exact Git blobs. The authored manuscript preserves the original mathematical body; its historic pending-review header is expressly superseded by the retained informal review. That existing AI-agent review is neither a formal Lean proof nor external human peer review.

The canonical statement asks whether the **actual union of real eigenvalues** of an independent-entry real interval matrix has at most its dimension many **connected components**. It explicitly allows singleton intervals, nonsymmetric matrices, zero eigenvalues, and matrices whose other eigenvalues are nonreal. Its equivalent closed-interval-cover wording is not substituted for the topological target.

## Definitions, assumptions and quantifiers

| Original object or quantifier | Lean meaning |
| --- | --- |
| Every integer n at least one | `ComponentBoundConjecture` quantifies all `n : ℕ` with `1 ≤ n` |
| Real n by n matrices | `RealMatrix n = Matrix (Fin n) (Fin n) ℝ` |
| L at most U entrywise | `EntrywiseLE L U` quantifies every row and column independently |
| Entire interval family | `InIntervalFamily L U A` is exactly `EntrywiseLE L A ∧ EntrywiseLE A U` |
| Actual nonzero real eigenvector | `HasRealEigenvalue A lam` uses `v ≠ 0` and `Matrix.mulVec`, with real scalar multiplication |
| Union over all admissible A | `realEigenvalueSet L U` existentially quantifies a matrix in the full family and an actual eigenpair |
| Number of genuine components | `componentCard S = Cardinal.mk (ConnectedComponents S)` with the subtype's inherited real topology |
| At most n, including potentially infinite quotients | Cardinal inequality against `(n : Cardinal)`; no use of `Nat.card` or assumed finiteness |
| Complete negative resolution | `not_componentBoundConjecture : ¬ ComponentBoundConjecture` |

The generic eigenvector/determinant bridge is stronger only in allowing dimension zero as well: the empty real vector space has no nonzero vector and the empty determinant is one, so both sides of the claimed zero-determinant equivalence are false. This extra harmless endpoint does not change the positive-dimensional original conjecture.

## Theorem 1 and its proof

The full authored and original manuscripts are `references/colbrook-intervals-2026-09-11/{manuscripts,submitted/manuscripts}/IV-06.tex`; the supplied preamble is `submitted/manuscripts/common.tex` in that archive. Theorem 1, its complete proof, and Section 2's scope are the mathematical input. The original proof uses four exact integer eigenpairs, three universally excluded separators, and the fact that a connected real subset contains each interval between its points.

| Source step | Complete exported obligation |
| --- | --- |
| Determinant-zero notation agrees with the canonical eigenpair definition | `eigenvalue_determinant_semantics`, using the actual characteristic determinant for every real square matrix |
| Two independent entries and seven fixed entries | `family_and_determinant_semantics` proves, rather than assumes, equivalence of the entire endpoint box with the displayed two-parameter family |
| Direct characteristic expansion | The same export proves the all-real identity `(lam - 25)*(lam^2 - 1) - a*(lam - 1) - b*(lam + 1)` for the actual determinant |
| Eigenpair table at −3, 0, 3, 25 | `witness_eigenpairs` proves admissibility, nonzero vectors, actual multiplication equations, and membership in the actual attained set |
| Determinant intervals at −1, 1, 12 | `witness_separators` proves both bounds for **every** admissible matrix and strict negativity, then actual set exclusions |
| Real connectedness forces intermediate points | `connected_component_intervals` proves interval containment from equality of Mathlib's actual component classes of an arbitrary real subset |
| Four separated included points | `four_components` proves representatives with the prescribed values, an injection of `Fin 4` into the quotient, and its cardinal lower bound |
| Dimension-three contradiction | `counterexample` proves valid original bounds and a strict component-cardinality violation; `not_componentBoundConjecture` refutes the original universal target |

The source also states the exact determinant **range**, including surjectivity onto the whole displayed interval for every real spectral parameter. The formal resolution needs only the true full-box bounds at three separators; that optional stronger range-surjectivity lemma is not advertised as an export. This does not narrow the original problem or any universal separator bound. No claim is made about exactly four components, a general replacement bound, component endpoints, or a single matrix possessing four eigenvalues.

## Exact computation plan and imported foundations

All finite data match the manuscript without adaptation. The independent diagnostic constructs the three-variable determinant coefficientwise by the permutation formula, rechecks each nonzero eigenpair, and evaluates all twelve separator-corner determinants. It also verifies an excluded separator between each of the six pairs of included values. These are diagnostics, not additional Lean assumptions.

The planned Lean proof will use `Matrix.exists_mulVec_eq_zero_iff` for the genuine singularity bridge; `ConnectedComponents`, `connectedComponent`, and continuous images for actual topology; `IsPreconnected.Icc_subset` for order-convexity in the reals; and `Cardinal.mk_le_of_injective` for the component count. The precise installed library declarations and elaborated instances are printed in the statement inspection. This avoids replacing eigenvalues or components with custom predicates whose assumed properties already contain the conclusion.

The sole planned LeanCert certificate is the strict real inequality −18 < 0, the least negative of the three actual determinant upper bounds. Kernel mode is mandatory, and its proof must materially feed the separator exclusion and final contradiction. There is no approximate determinant, root, eigenvalue or topology oracle. Algebraic identities and linear full-box estimates need no subdivision.

## Attribution, licensing, review and duplicate scope

Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge, is the original mathematical author recorded by the repository. George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, is the formalization author. The new code is AI-assisted and uses the supplied Apache-2.0 license; existing source authorship is not reassigned. No George email is added.

The shared workflow adapts Tau Ceti Review at `afb424eda89e8ac96d9eb69f6a88972055a4cd1b`, as documented in `docs/lean/REVIEW.md`, and the statement/proof separation and numerical-target organization of the pinned Schiffer and Forsythe examples in `docs/lean/README.md`. No proof code from those examples has been copied into this statement package. Mathlib and LeanCert retain their own licenses and authorship.

The bounded public duplicate audit inspected all 83 returned branch heads across upstream and its seven listed forks, representing 72 distinct commits, and all 63 returned upstream PRs plus the fork PR lists. Seventy-one head trees were inspected from exact Git objects; the remaining tree was obtained from an untruncated GitHub tree response. No path identifiable as an IV-06 Lean package was found. The only IV-06 PR match was the existing informal resolution, PR 62. This is a check of the public heads and PRs observed at the recorded time, not a claim about deleted/private branches, unadvertised filenames, unpublished work, or historical priority. Raw receipts are retained with the duplicate-audit report.

Two independent statement approvals are required before proof implementation. Complete formal proof, two independent final reviews, and actual Linux kernel/Comparator verification remain pending.
