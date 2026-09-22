# Canonical campaign inventory and independent source assessment

Date: 2026-09-22. Source base: `54f93060c0c4e5dab81096c6496e0d2b4251f3ef` (`origin/main` when this worktree was created). Reviewer: `/root/canonical_inventory`, an independent Codex AI agent assigned to read-only inventory and mathematical source assessment, subsequently authorized to record these notes. This is not a formal-statement approval, a Lean verification, external human peer review, or an official Tau Ceti service report.

## Inventory method and result

Read `problem_ids.json`, then read exactly the registered canonical README for each ID. Extract only the first `**Status:**` field. Review snapshots, copied verification archives, reference manuscripts, category indexes and generated summaries are excluded. The registry SHA256 is `d7f9925a483d40030ef266917bc8e413dac6d45530ad5515da506ffe9583e763`.

| Canonical status | Entries |
|---|---:|
| Lean verified | 63 |
| Solved | 43 |
| Partially resolved | 70 |
| Open | 41 |
| Total registered IDs | 217 |

None of the 43 canonical Solved directories contains a `lean/` directory at this base. This says nothing about unpublished branches, ongoing tasks or work outside the canonical directories. The existing 63 Lean verified entries must be preserved; these notes have not rerun their evidence or audited all their statements.

| Category | Remaining Solved canonical IDs |
|---|---|
| Arithmetic and complexity | AA-01 |
| Intervals and absolute-value equations | AV-01, AV-02, IV-02, IV-04, IV-05 |
| Eigenvalues and inverse problems | IE-08, IE-10, KE-03, SP-11, SP-12, SP-13 |
| Linear systems and elimination | IE-12, IE-21, IE-22, IE-26 |
| Matrix discrepancy and optimization | MD-03, MD-04, MD-06 |
| Matrix functions and stability | MF-03, MF-08 |
| Matrix inequalities and norms | MI-16 |
| Nonnegative and positive factorizations | NM-03, PF-04, PF-05 |
| Randomized and low-rank approximation | RA-04, RA-05, RA-10, RA-12, RA-13, RE-05, RE-06, TR-07, TR-08, RA-19 |
| Tensor computations | TR-04, TR-06, TR-13, TR-14, TR-17, TR-20, TR-26, TR-27 |

The initial working checkout was stale relative to this base: its 55 Solved / 50 Lean verified inventory must not be reused. In particular, NR-04, SP-15 and MF-14 are already Lean verified on this base. MI-24 and MI-28 are all-dimensional affirmative statements, and also already Lean verified here; they are not outstanding finite counterexample opportunities.

## Infrastructure already present

`docs/lean/README.md` and `docs/lean/REVIEW.md` specify separate trusted Challenge and Solution environments, two independent statement reviews before proof implementation, two independent final reviews, complete original-target correspondence, kernel-mode LeanCert, real sandboxed Comparator, transitive permitted-axiom checks, reproducible Linux evidence, and truthful metadata. Their retained operational audit is bound to `214c142d6bfe0f0c338808f188062acbbad0fb19`. It is infrastructure evidence and does not verify any new mathematical target.

The documentation pins Schiffer, Forsythe, LeanCert, Comparator, the formalization metadata standard and the Tau Ceti rubric adaptation. The coordinating agent is auditing those tools and current operational availability separately; this report does not substitute for that audit.

## Candidate assessment

| Candidate | Full retained target and useful reduction | Main unproved formal dependency |
|---|---|---|
| MF-03 | Every normalized diagonal Padé order for the complex entire series, no pole on the closed radius-three disk and error at most two. The source uses exact orders 1–15 and one uniform tail argument for all orders at least 16. | Infinite-product coefficients, Schur/tableau denominator formula and dual Jacobi–Trudi bridge; finite certificates alone do not cover all orders. |
| TR-27 | One reduced irreducible nondegenerate complex projective variety with border rank below rank but no saving at the exact unmerged tensor square. Specialize the source to a twelve-coordinate projected rational curve and ranks 3 and 9. | Zariski closedness of the projected parameter image and its correspondence to the chosen variety, plus arbitrary complex tensor-decomposition lower bounds. |
| RA-12 / RA-13 | Both links of their complete Gaussian/Gamma probability chains, all spectra and sample counts, at the stated non-strict thresholds. | Substantial distribution, convolution and tail comparison theory. Their retained auxiliary counterexamples do not resolve the canonical statements. |
| SP-13 | Arbitrary complex trace-norm-small perturbations preserve the Hermitian spectral distribution, without norm bounds. | Dimension-independent weak-type triangular truncation theorem and measure/spectral-limit framework. Formalizing only the limiting deduction would be conditional. |
| IV-02 / IV-04 / MF-08 | Exact binary-model complexity classifications, not just algebraic gadget identities. | Polynomial-time reduction and computation models, together with all promised output/regularity conventions. |

MF-03 and TR-27 are reasonable next statement-design candidates because their source proof chains can be described completely. Neither is a small scalar-certificate task. A finite witness in TR-27 does not remove its global geometric and arbitrary-decomposition obligations. No trivial remaining finite-matrix counterexample was identified in this inventory.

## TR-27 independent mathematical source assessment

Read the complete current manuscript, the unchanged canonical target, and the historical independent report. Also checked the primary [Ballico–Bernardi–Gesmundo–Oneto–Ventura paper, introduction and Conjecture 1.1](https://arxiv.org/html/1909.03811v2): its variety convention includes projective, irreducible, reduced and linearly nondegenerate, and its product is the Segre image in the ordinary tensor product. The historical review is supporting provenance, not a substitute for this source inspection.

No substantive mathematical gap was found in the manuscript's negative resolution of this exact target. The following steps were independently checked:

1. The annihilator polynomial proves that the tangent vector `e₁` cannot be a sum of at most eleven rational-normal-curve vectors of degree twelve, including arbitrary complex parameters, zero and the parameter at infinity. Its coefficient of degree one is nonzero; when infinity occurs its coefficient of degree twelve is zero.
2. The center `z = e₁ − c(1) − c(2) − c(3)` therefore cannot be spanned by eight curve points. This is the only center-rank bound needed for the canonical counterexample.
3. Any relation among at most eight distinct projected curve points lifts either to a relation among their rational-normal-curve lifts, excluded by Vandermonde independence, or to a forbidden expression for the center. Thus the needed independence holds for every such set, not merely generic sets.
4. The projected point has a displayed three-term expression. Any expression of length at most two would give a relation in a union of at most five projected points, contradicting the preceding independence. In particular it is nonzero and lies off the curve.
5. The difference quotient of the curve at zero yields border rank at most two. Algebraically, substitution into every polynomial vanishing on the rank-at-most-two cone produces a univariate polynomial vanishing for all nonzero parameters and hence at zero. This avoids interval computation and analytic limits without changing the Zariski conclusion.
6. In a hypothetical square decomposition of length at most eight, the distinct points in each separate tensor factor are independent. Contraction places the projected point in each span. Each coordinate expansion needs at least three nonzero coefficients, so its tensor square has at least nine nonzero product-basis coordinates. At most eight summands cannot supply those nine coordinates, even with repetitions, cancellations, arbitrary scalars or unrelated choices in the two factors. The displayed nine-term expansion supplies equality.
7. The image of the projective rational normal curve under projection from a center outside the curve is a closed irreducible projective image. Taking its reduced structure is legitimate. Surjectivity of the quotient and spanning of the original curve prove nondegeneracy. These facts are genuine proof obligations, not assumptions to insert into a formal boundary.

The essential formalization warning is step 7: defining the desired curve as the Zariski closure of a parameterized image does not by itself prove that every point of that closure has the required parametrization. The lower bound in steps 3 and 6 must hold on the entire chosen projective variety. An image/closure equality or an equivalent complete description is necessary.

The canonical conjecture does not require smoothness, rationality, exact center border rank, arbitrary finite delay, or eventual saving. Those are correctly argued source strengthenings, but may be omitted from a deliberately smaller counterexample formalization with explicit scope disclosure. In particular, the exact Hankel determinant `5184` is not needed for the complete canonical negative answer. It must not be presented as the square-rank lower-bound certificate.

## Library reconnaissance and limits

A preliminary read of the locally available Mathlib source at `/private/tmp/mf21-mathlib-source-20260920/Mathlib` found `Projectivization` representatives, independence and subspaces; `Module.Basis.tensorProduct` and its coefficient formula; multivariate-polynomial zero loci, vanishing ideals and Nullstellensatz; and scheme-level properness of `Proj`. It did not establish an immediately usable bridge between elementary complex projective points and the scheme-level closed-image theorem. These are API leads, not a claim that the final project's exact pinned imports have been validated.

Existing MF-14 has polynomial zero-locus and Euclidean-to-polynomial-closure techniques; RA-20 has reduced coordinate-ring and geometric statement conventions. Their existing verifications should remain intact. Reuse should preserve licenses and attribution and should import or copy only actual reusable lemmas after checking their pinned dependencies and scope.

## Source binding and attribution

SHA256 of exact bytes read at the source base:

| File | SHA256 |
|---|---|
| `tensor-computations/TR-27/README.md` | `111ccd36436f926608d1e604ed974d82dfe9ece400c7ac2ce8710d96d00b2e00` |
| `references/colbrook-tensor-metrics-rank-2026-09-11/manuscripts/tr27_solution.tex` | `e554971c970e05efb61675f35d66bdc4847266fe5eba86e8cb445043fb83be67` |
| `references/colbrook-tensor-metrics-rank-2026-09-11/verification/reviews/TR-27-review.md` | `64f31be7ebd746a6ec7ac188cc9b3523a36b81c9af9082a423aa3c2c75196cfa` |
| `matrix-functions-and-stability/MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| `references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-03.tex` | `312e90a79405a6cf0b116d5e3cc402a242107104f56cfb5abf542a18ff36247b` |

Matthew J. Colbrook retains original proof and construction attribution for TR-27 and MF-03, with Department of Applied Mathematics and Theoretical Physics, University of Cambridge affiliation. Any subsequent formalization requested for this campaign is to credit George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, and disclose AI assistance and review scope. No contact email is added. No canonical page, status or permanent identifier was modified for this assessment.
