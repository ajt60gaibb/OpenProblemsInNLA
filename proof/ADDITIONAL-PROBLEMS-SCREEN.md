# Screen of the supplied additional problems

Screened **2026-09-08** against the current 125-entry catalog and primary literature.
The 43-candidate [user proposal](proposals/ADDITIONAL_PROBLEMS.md) is preserved
as supplied. Its older overlap annotations are superseded by this statement-level
screen. Its relative references to `INDEX.md`, `SCREENING_NOTES.md`, and
`records.json` refer to unsupplied companion files, not this repository’s navigation.

**Result: 22 new entries, 15 duplicates or already-covered candidates, one stronger
formulation newly grouped into an existing entry, and five withheld/excluded
candidates. The catalog now contains 147 / 1,000 entries.** “Duplicate” below
includes a narrower case already covered and a companion previously grouped.
No proposal has been dropped without a recorded disposition.

Each new entry has Markdown, standalone LaTeX, a compiled PDF, both requested
editorial ratings, references and a dated bounded literature check. The new
matrix-discrepancy-and-optimization category keeps the relevant signing and
semidefinite questions visible. A source-stated exact-value or construction
problem is labelled as such, rather than recast as an affirmative conjecture.

## Every candidate

| Proposal | Disposition / catalog entry | Source-fidelity or counting decision |
| --- | --- | --- |
| ADD-001 — Precision needed for CG to terminate accurately in n steps | Added [IE-20](../linear-systems-and-elimination/IE-20/README.md) | Explicit CG implementation and arithmetic-model specialization. |
| ADD-002 — A stable O(nk) algorithm for the bidiagonal SVD | Withheld | Repeated uncounted IE-09 lead; uniform precision/cost model remains unresolved. |
| ADD-003 — All-future Ritz-value interlacing in block Lanczos | Already covered by [KE-04](../eigenvalues-and-inverse-problems/KE-04/README.md) | Same strict interlacing statement at every later block-Lanczos iteration. |
| ADD-004 — Can rank deficiency cause exact DR-BCG to break down? | Excluded: later resolution claim | Later primary author manuscript reports breakdown freedom. |
| ADD-005 — Higher-order gaps in randomized block Krylov bounds | Already covered by [RA-04](../randomized-and-low-rank-approximation/RA-04/README.md) | Gap-dependent companion already explicitly grouped in RA-04. |
| ADD-006 — Concave-function spectral-error transfer | Added [RA-08](../randomized-and-low-rank-approximation/RA-08/README.md) | Spectral/concave/ordered open cell; source real symmetric field. |
| ADD-007 — Concave-function Frobenius-error transfer | Added [RA-09](../randomized-and-low-rank-approximation/RA-09/README.md) | Frobenius/concave/ordered open cell, with its stronger premise. |
| ADD-008 — Constant-loss nuclear-error transfer without Loewner ordering | Added [RA-10](../randomized-and-low-rank-approximation/RA-10/README.md) | Disclosed nuclear-norm specialization of fixed-loss transfer. |
| ADD-009 — Minimax trace-estimation complexity with Kronecker queries | Added [RA-11](../randomized-and-low-rank-approximation/RA-11/README.md) | Editorial minimax formulation for full-vector Kronecker queries. |
| ADD-010 — Audenaert’s norm-compression conjecture | Already covered by [MI-01](../matrix-inequalities-and-norms/MI-01/README.md) | Contained square-block case of MI-01’s rectangular-block statement. |
| ADD-011 — Sharp best-rank-one approximation ratio for general tensor formats | Added [TR-19](../tensor-computations/TR-19/README.md) | Exact general real tensor-format constant; known cases retained. |
| ADD-012 — Border Comon conjecture | Already covered by [TR-10](../tensor-computations/TR-10/README.md) | Same border-rank Comon conjecture, including limiting convention. |
| ADD-013 — Gaussian type-2 bound for tensor injective norms | Already covered by [TR-18](../tensor-computations/TR-18/README.md) | Same Type-2 tensor approximation target. |
| ADD-014 — Sharp Lovász-theta asymptotics for dense Erdős–Rényi graphs | Added [MD-01](../matrix-discrepancy-and-optimization/MD-01/README.md) | Conjecture 17 in the archived 2025 collection. |
| ADD-015 — Sharp Lovász-theta asymptotics for random circulant graphs | Added [MD-02](../matrix-discrepancy-and-optimization/MD-02/README.md) | Conjecture 18, with symmetric difference-class sampling. |
| ADD-016 — Vinzant’s limiting injectivity probability | Already covered by [FR-05](../frames-and-matrix-designs/FR-05/README.md) | Same limiting probability in complex phase retrieval. |
| ADD-017 — Uniform exponential ill-conditioning at minimal real phase-retrieval redundancy | Already covered by [FR-04](../frames-and-matrix-designs/FR-04/README.md) | Same uniform exponential stability obstruction for full-spark measurements. |
| ADD-018 — No complete set of mutually unbiased bases in dimension six | Already covered by [FR-06](../frames-and-matrix-designs/FR-06/README.md) | Same impossibility of seven mutually unbiased bases in dimension six. |
| ADD-019 — Zauner’s SIC existence conjecture | Already covered by [FR-07](../frames-and-matrix-designs/FR-07/README.md) | Same all-dimension SIC existence statement. |
| ADD-020 — Equiangular tight frames of redundancy two in every complex dimension | Added [FR-09](../frames-and-matrix-designs/FR-09/README.md) | Glazyrin’s Conjecture 1; all dimensions and 2d vectors. |
| ADD-021 — Paley ETF beyond square-root sparsity | Already covered by [FR-03](../frames-and-matrix-designs/FR-03/README.md) | Equivalent Paley frame description and beyond-square-root target. |
| ADD-022 — Optimal deterministic RIP matrices | Grouped stronger target in [FR-01](../frames-and-matrix-designs/FR-01/README.md) | Stronger optimal-row formulation added inside FR-01; no extra count. |
| ADD-023 — Optimal row count for a subsampled Walsh RIP matrix | Added [FR-10](../frames-and-matrix-designs/FR-10/README.md) | Quantitative sampling-gap restatement; replacement convention explicit. |
| ADD-024 — Nobori’s strengthened three-factor commutator inequality | Added [MI-13](../matrix-inequalities-and-norms/MI-13/README.md) | Nobori Conjecture 3.1, with the spectral norm on the middle factor. |
| ADD-025 — The fundamental Lu–Wenzel conjecture in spectral form | Added [MI-14](../matrix-inequalities-and-norms/MI-14/README.md) | Complex Lu–Wenzel spectral conjecture; equivalent forms grouped. |
| ADD-026 — A sum-of-squares certificate for the Toeplitz commutator inequality | Added [MI-15](../matrix-inequalities-and-norms/MI-15/README.md) | Real Toeplitz SOS certificate question, distinct from nonnegativity. |
| ADD-027 — The symmetric nonnegative inverse eigenvalue problem in order five | Withheld | No precise nontrivial completion criterion for fixed-order classification. |
| ADD-028 — Lieb’s permanent-dominance conjecture | Already covered by [MI-11](../matrix-inequalities-and-norms/MI-11/README.md) | Same generalized-matrix-function permanental dominance statement. |
| ADD-029 — Chollet’s permanent conjecture beyond the currently claimed small orders | Already covered by [MI-10](../matrix-inequalities-and-norms/MI-10/README.md) | Same Hadamard-product permanent inequality. |
| ADD-030 — Marcus’s permanent-of-block-permanents inequality | Already covered by [MI-12](../matrix-inequalities-and-norms/MI-12/README.md) | Same permanent-of-block-permanents inequality. |
| ADD-031 — Maximum permanent on a positive semidefinite unitary orbit | Added [MI-16](../matrix-inequalities-and-norms/MI-16/README.md) | Exact extremal-value problem; refuted equal-diagonal rule omitted. |
| ADD-032 — Lih–Wang permanent convexity toward the flat matrix | Added [MI-17](../matrix-inequalities-and-norms/MI-17/README.md) | Published Lih–Wang statement; journal partial results corrected. |
| ADD-033 — The remaining low-dimensional Dittert inequalities | Withheld | Newer full-range proof claims prevent an unqualified open classification. |
| ADD-034 — Marcus–de Oliveira determinantal conjecture | Already covered by [MI-05](../matrix-inequalities-and-norms/MI-05/README.md) | Same normal-matrix determinant convex-hull assertion. |
| ADD-035 — Komlós discrepancy conjecture | Added [MD-03](../matrix-discrepancy-and-optimization/MD-03/README.md) | Komlós matrix signing conjecture, with one universal constant. |
| ADD-036 — Beck–Fiala discrepancy conjecture | Added [MD-04](../matrix-discrepancy-and-optimization/MD-04/README.md) | Classical incidence-matrix conjecture; its implication from Komlós disclosed. |
| ADD-037 — The sharp Spencer discrepancy constant | Added [MD-05](../matrix-discrepancy-and-optimization/MD-05/README.md) | Exact sharp constant, with the asymptotic companion grouped. |
| ADD-038 — Hadamard existence in every admissible order | Already covered by [FR-08](../frames-and-matrix-designs/FR-08/README.md) | Hadamard existence already admitted as FR-08. |
| ADD-039 — Ryser’s circulant Hadamard conjecture | Withheld | Standing circulant-Hadamard proof claims remain unadjudicated. |
| ADD-040 — Deterministic polynomial-time commutative Edmonds problem | Added [AC-09](../arithmetic-and-complexity/AC-09/README.md) | Commuting variables, rational input, deterministic polynomial bit cost. |
| ADD-041 — An explicit Valiant-rigid family | Added [AC-10](../arithmetic-and-complexity/AC-10/README.md) | Disclosed rational-field and polynomial-output specialization. |
| ADD-042 — Optimal growth after inversion of an exponentially stable generator | Added [MF-17](../matrix-functions-and-stability/MF-17/README.md) | Fixed-M growth formulation supported by uniform bounds. |
| ADD-043 — Global synchronization of a random cubic graph | Added [MD-06](../matrix-discrepancy-and-optimization/MD-06/README.md) | Cubic-graph conjecture; phase torus and non-strict local minima. |

## Why five candidates do not count

**ADD-002, selected bidiagonal singular triplets.** The [August Simons report](https://arxiv.org/html/2602.05394v3),
Problem 3.8, still asks for a stable $O(nk)$ method. This repeats the previously
uncounted IE-09 lead. The supplied formulation does not fix a uniform
precision/operation-cost convention: allowing an arbitrary dependence on a fixed
precision can make the dimension asymptotic vacuous under a small-$nu$ restriction.
No solution is claimed; the faithful computational target still needs clarification.

**ADD-004, DR-BCG breakdown.** The older [Block CG algorithms revisited](https://arxiv.org/abs/2502.16998),
Algorithm 5 and §8, poses the question. Meurant–Papež–Tichý’s later author manuscript,
[*Block conjugate gradient methods with error norm estimates for least squares problems*](https://www.gerard-meurant.fr/Meurant_Papez_Tichy_2025.pdf),
p. 4 following Algorithm 2, expressly reports nonsingularity of the required
$S^TAS$ matrices even when QR residual factors are singular. Reference 13 on
p. 30 cites Meurant–Tichý, *Dubrulle’s variant of the block conjugate gradient
algorithm*. That separate proof manuscript and its QR-completion conventions were
not independently retrieved or certified here. The later primary resolution claim
is enough to exclude this candidate from an unqualified open list; this screen
does not claim to have verified its proof.

**ADD-027, order-five symmetric nonnegative inverse spectra.** Jin–Ke–Sui’s
[August 2026 paper](https://arxiv.org/html/2608.19435v1), §§1–2 and §5,
leaves a structural classification region open. Its new necessary inequality is
not asserted to be sufficient on the complementary side. However, “complete
effective characterization” with no defined output restriction is not an adequate
new target: fixed-dimensional real quantifier elimination already applies to the
fifteen symmetric entries, nonnegativity, and characteristic-polynomial coefficient
constraints. The proposal excludes generic elimination without specifying a precise
alternative completion criterion. Requiring “simple” conditions would leave that
criterion undefined. This is a genuine research direction, withheld for statement
precision rather than declared solved or equivalent to the stochastic-uniqueness
question IS-02.

**ADD-033, Dittert in dimensions 5–16.** [Kafidov’s July 2026 preprint](https://arxiv.org/html/2607.19439v1),
Theorem 1.1, claims the order-sixteen case. More broadly,
[do Nascimento’s primary working-proof repository](https://github.com/pedromnasc/dittert-conjecture-proof)
contains an [assembled all-dimension theorem](https://github.com/pedromnasc/dittert-conjecture-proof/blob/main/unified/dittert_unified_proof.tex)
and [explicit review limitations](https://github.com/pedromnasc/dittert-conjecture-proof/blob/main/PROOF_STATUS.md).
This is a concrete unrefereed claim supported by proof material, not a theorem
certified by this screen. It prevents labelling the proposed remaining range
cleanly open without adjudication. [Pang’s earlier 2026 claim](https://arxiv.org/abs/2606.01531)
covered orders at least seventeen and was already acknowledged in the proposal.

**ADD-039, circulant Hadamard.** The existing withholding decision continues.
Current primary records retain Morris’s [2023 proof claim](https://arxiv.org/abs/2302.08346)
and Orozco López’s [2019 proof claim](https://arxiv.org/abs/1907.12683), with no
withdrawal shown. Their validity was not adjudicated. This screen asserts neither
that those claims are accepted proofs nor that the conjecture can be listed
unconditionally as open. Ordinary Hadamard existence is already FR-08.

## Formulation and status corrections preserved in the entries

- IE-20 fixes an unpreconditioned CG recurrence, stored inputs, accumulation order,
  an adversarial relative-error model, early stopping, and a true-residual
  backward-error criterion. Its precision threshold is an editorial specialization
  of Simons Problem 2.17, not an implementation-independent theorem statement.
- RA-08–10 use the primary paper’s real symmetric PSD field and consistent
  eigenvectors for matrix/function truncations. The proposal’s complex field is
  broader than the verified source. RA-09 retains the stronger squared-norm-defect
  premise; RA-10 seeks one constant independent of all input parameters.
- RA-11 allows full-vector $Mv$ responses and arbitrary adaptive Kronecker queries.
  The cited trace lower bound is for a conditioned scalar $v^TMv$ oracle. Both
  restrictions matter; it is not a lower bound for the displayed minimax problem.
- FR-01 preserves its original $s\operatorname{polylog}N$ target and separately
  attributes ADD-022’s optimal $s\log(eN/s)$ target to a quantitative reading of
  Rao’s introduction. Bandeira’s Open Problem 5.1 is only a related weaker target;
  the original target comes from IITK Question 21(1). Rational rounding requires
  sufficiently fine entries of polynomial bit length, not fixed entrywise accuracy.
- FR-10 explicitly fixes with-replacement Walsh sampling. The published lower
  bound is stated for Bernoulli inclusion in an intermediate sparsity range.
  It is not copied as an all-parameter formula or transferred to cyclic DFTs.
- MI-14 and MI-15 give both published and arXiv conjecture locators, whose numbering
  differs. MI-17 uses the 2024 published Lih–Wang theorems: the order-four result
  and a conditional order-six result on a restricted interval are narrower than
  the old preprint abstract. No unrestricted order-six proof is claimed.
- MD-03 and MD-04 remain distinct classical conjectures, with the implication
  from Komlós to Beck–Fiala disclosed. MD-05 groups the asymptotic Spencer
  companion and excludes the source’s refuted odd-Sylvester assertion.
- AC-09 distinguishes commutative rational symbolic rank from noncommutative rank.
  AC-10 explicitly selects rational perturbations and polynomial binary output;
  results over other fields are not assumed equivalent.
- MF-17 concerns the surviving sharp growth question, not the inverse-generator
  existence question already resolved in August 2026. Its fixed-$M$ formulation is
  supported by Batty–Gomilko–Tomilov’s explicit uniform upper bound (Corollary 5.7)
  and the new normalized lower examples. No conjectured sharp rate is invented.
- MD-06 uses a phase torus and ordinary, possibly non-strict local minima.
  Large-degree expanders, a random-graph-process theorem and dense-degree results
  do not settle uniform random cubic graphs.

## Verification scope

Three research subagents screened disjoint supplied ranges; the root screened
the remaining range and integrated the entries. Independent follow-up audits
checked the core arithmetic/query formulations, theta/frame/RIP statements, and
matrix-inequality source statements. Bibliographic corrections include the distinct
author lists of the 2024 and 2025 annual Randomstrasse archives and the circulant
theta paper. No conjecture was attacked or solved. Each entry states the searches,
current source versions and limits of its evidence; no located solution is not a
proof of openness. Historical sources without a recent explicit reaffirmation
remain visibly identified.

The 22 new PDFs contain 23 pages; the revised FR-01 remains one page. All 24
new or changed pages were visually checked after compilation. The collection
now contains 147 PDFs and 152 pages. Navigation and required metadata were checked.
