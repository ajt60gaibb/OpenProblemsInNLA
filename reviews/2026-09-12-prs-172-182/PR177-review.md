# PR #177 — independent KE-01 mathematical and evidence review

Reviewer: Codex AI agent `/root/audit_tensors_complexity`. Date: 12 September 2026. This is an independent informal AI audit, not external human peer review or Lean verification.

**Verdict: PASS for the stated partial results.** The full arbitrary sparse, bounded-tail KE-01 target remains unresolved. No mathematical or publication blocker was found in the reviewed contribution.

Reviewed head: `8b056c604f53070a7d351743cdc4784c1403aad8`, clean read-only worktree `/private/tmp/nla-audit-177`. Published comparison base: `f41f1f9ffa2171550d4bb795862c6170c4f26070`. No repository, git, or remote mutation was performed. Submitted reviews were not used as proof authority.

## Target and publication scope

The canonical target retains its original path, KE-01 ID, hypotheses, exact-arithmetic model, physical residual, success probability, and additive target cost. It asks for an algorithm for arbitrary nonsingular sparse real matrices with `sigma_(k+1)/sigma_n <= kappa`, at cost polylogarithmically larger than `k^omega_0 + nnz(A) kappa`, with a fixed attained multiplication exponent `omega_0 > 2`. The canonical text from “Context and notation” onward is byte-identical to the published base; difficulty, importance, rating rationale, and the 217-entry ID registry are unchanged.

The new status is appropriately **Partially resolved**. The sparse CGLS regimes are actual subfamilies of the original target. The stronger restricted theorem additionally needs explicitly sparse SPD input and an exactly flat tail. Its nonsymmetric corollary openly charges `W_A = sum_i nnz(A[i,:])^2`, which can be much larger than input sparsity. The conditional final proposition is not presented as a constructed general preconditioner.

## Independent mathematical assessment

I read the complete mathematical manuscript, `references/holden-ke01-2026-09-12/report.tex`, and checked the following arguments rather than relying on the packaged PASS statements.

| Result and source location | Assessment |
| --- | --- |
| Theorem 2.1, §§2.1–2.3, starting at line 100 | Valid deterministic CGLS bound. The normal-equation energy norm is exactly the original physical residual. An outlier-annihilating polynomial has absolute value at most one on the remaining positive spectrum; its Chebyshev factor yields the stated tail iteration count. Exact flatness admits the degree `k+1` annihilator. Termination at dimension `n` and residual-based stopping avoid an assumed spectral oracle. |
| Corollary 2.2, §2.4, line 189 | The four regimes correctly absorb the otherwise troublesome `nnz(A) k` term, or use dense elimination when `n <= 2k`. Input reading is within the displayed bounds for nonsingular matrices. |
| Propositions 3.1–3.3, line 200 onward | The sparse matrix with dense normal matrix, the low-row sketch/identity obstruction, and the rank-one Nyström residual formula are correct. They refute the specific proposed deductions; they are not lower bounds for all algorithms or all preconditioners. |
| Theorem 4.1, §4, line 280 onward | The restricted flat-tail SPD construction and its cost/probability accounting are sound. Details checked below. |
| Corollary 5.1, §5, line 487 | Forming `A^T A` is charged to `W_A`, not silently to `nnz(A)`. The reduced SPD accuracy is sufficient for the original residual, and its logarithm is controlled by the original condition number and dimension. |
| Proposition 6.1, §6.2, line 539 | The preconditioner implication is valid under all its stated setup, application, and spectral hypotheses. The manuscript explicitly leaves construction of such a preconditioner open. |

For Theorem 4.1, write `M = alpha I + R` with `R >= 0` and rank at most `k`. When the dense fallback does not apply, a `(2k+1)`-dimensional principal block gives `alpha` as the only characteristic root with multiplicity at least `k+1`. Repeating monic gcd with the derivative `k` times isolates a power of `z-alpha`; its coefficients recover the shift using field operations. A fixed positive gap between 2 and the chosen `omega_0` accommodates fast polynomial arithmetic. No exact algebraic-root oracle is assumed.

On the first good embedding event, the selected positive principal block `W` and sparse factor `F` give the exact identity `R = F W^{-1} F^T`. I checked the range argument through `R^(1/2) Omega`, and the recursive PSD principal-rank selection, including singular sketches. The second embedding supplies a constant-condition SPD preconditioner for `K = alpha W + F^T F`. Woodbury then reduces the solve to this smaller system. The manuscript's energy-norm error transfer, upper estimate `alpha + tr(R)`, and finite iteration cap deliver the physical residual without uncharged spectral estimates.

The probability guarantee is a union bound on two embedding failures of at most `1/200` each. Bad sketches still leave the selected principal block and inner preconditioner positive definite where used. Rank zero is handled explicitly. The fixed setup and iteration cap therefore bound work even on failure; the algorithm does not retry until success. The proof covers overestimated rank, `k=0`, `n<=2k`, and exactly flat tails. Replacing exact flatness by an arbitrarily small positive tail perturbation would invalidate its rank argument, and the manuscript explicitly recognizes this limitation.

## Primary-source checks

I checked the source problem in [the workshop report, Problem 2.5](https://arxiv.org/html/2602.05394v3), and the two main external algorithmic primitives: [Nelson–Nguyen, OSNAP, Theorem 9](https://arxiv.org/pdf/1211.1002) and [Neiger–Pernet, Theorem 1.1 and §1.1](https://arxiv.org/html/2010.04662). The former supplies the stated polylogarithmic column sparsity and embedding dimension at fixed distortion; its application to squared norms permits the manuscript's constant bounds. The latter supplies characteristic-polynomial computation for a specified matrix-multiplication bound with exponent greater than two. The proof uses the primitives as mathematical algorithms; the ordinary dense kernels in the small executable tests do not claim their asymptotic performance.

I also checked the relevant regularization scope in [Dereziński–Sidford, Corollary 13](https://arxiv.org/html/2507.11724). Averaged tail energy cannot simply be replaced by a maximum-tail singular value; the distinction used in the manuscript is real. This audit is not an exhaustive priority search, and no novelty or priority claim is needed for acceptance of the recorded partial result.

## Executable evidence

Before execution I read the complete `exact_arithmetic.py`, `verify_exact.py`, and `solve_json.py`. Their relevant behavior is local exact arithmetic and local JSON/CSV output, with no remote action or dependency installation. I copied the reference directory to `/private/tmp/nla-177-independent-9impxbbo/ke01` and ran the verifier and example solver there using Python 3.12.14 and SymPy 1.14.0 from `/private/tmp/nla-batch-python/bin/python`.

The fresh run passed: 66 CGLS cases, 209 Chebyshev cases, 8 flat-tail reconstruction cases, 28 inner-PCG cases, 5 sparse/dense-Gram cases, 9 Nyström cases, and 3 row-sketch cases, together with the exact-flatness discontinuity example. The example JSON solver also passed. Evidence is in `fresh-exact.log`, `fresh-results/exact_checks.json`, `fresh-results/cgls_cases.csv`, and `fresh-solver.json` under that scratch directory.

These are finite exact diagnostics supporting the identities and boundary handling. They do not establish the general probability or asymptotic cost; those rest on the written proof and cited primitives. In particular, retries used to obtain small algebraic test fixtures are not evidence for the bounded-work randomized theorem.

## Attribution, preservation, and PDF review

All 13 entries in the retained submission manifest matched. The attributed report's mathematical body, beginning with its first section, is byte-identical to the frozen submitted manuscript. Executable mirrors are byte-identical to their retained submitted versions. Changes to the report front matter and PDF authorship are disclosed; AI assistance and the absence of formal or external human verification remain explicit. Original problem and prior-result credits are retained. The official [Simons Foundation profile](https://www.simonsfoundation.org/people/sidney-holden/) supports the supplied affiliation.

Using the PDF skill's render-and-inspect procedure, I visually inspected both pages of `linear-systems-and-elimination/KE-01/problem.pdf`. Equations, status limits, references, and page breaks are readable, with no clipping, overflow, or missing glyph found. Renders are retained in `/private/tmp/nla-177-181-pdf-review/KE-01-1.png` and `KE-01-2.png`. The complete report mathematics was reviewed in TeX; this does not claim a page-by-page visual audit of its separate longer PDF.

**Acceptance boundary:** record the proved subfamilies and supporting obstructions, retaining the full original target as partially resolved. This review does not certify a full KE-01 solution, formal proof, independent human endorsement, or historical novelty.
