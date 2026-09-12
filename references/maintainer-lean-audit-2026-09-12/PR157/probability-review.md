# PR #157 — independent RA-03 probability and statement review

**Verdict: PASS for English-to-Lean fidelity, probability semantics and inspected proof source.** I found no blocking scope or mathematical defect. This formalization proves a complete negative answer to the original universal RA-03 conjecture. Promotion to `Lean verified` also requires the separate authenticated CI statement, axiom and kernel-verification gate being assessed by the integration owner.

Reviewer: OpenAI Codex AI agent `/root/audit_functions_randomized`, independently reviewing this PR; not its formalization implementer. Phase: final statement-fidelity and proof-source review. Date: 2026-09-12. Exact reviewed head: `a49725405f153f8756610f52ce6cbc6463c51616`, checked in `/private/tmp/nla-lean-audit-157`. No repository files or Git state were changed; no contributor code or workflow was executed.

Locations below are relative to `randomized-and-low-rank-approximation/RA-03/lean/` unless otherwise indicated. I read Definitions, Challenge, Solution and the complete Proof, along with the canonical statement, numerical targets, configuration, dependency manifest, attribution and current CONTRIBUTING/Lean review requirements. Submitted referee PASS labels were not used as evidence for the conclusions below.

## Original target and quantifiers

The canonical `../README.md:54–72` asks whether the specified randomized LU residual obeys the factor-2^k squared Frobenius bound for every complex m-by-n matrix, all positive dimensions, and every integer 1 ≤ k ≤ min(m,n). The pre-formalization statement at repository revision `5adea969c17391693978ada2674d25bb5c3daeb1` has the same mathematical target. I also checked the primary [Gilles–Wilber source](https://arxiv.org/html/2601.22344v1): equations (1) and (3), Algorithm 1, and the conjecture following Theorem 3 specify this residual update, joint entry sampling, and proposed improvement from 4^k to 2^k.

`NLA/RA03/Definitions.lean:82–85` retains every canonical quantifier. It does not impose Hermitian symmetry, positive definiteness, real entries, nonsingularity, nonzero entries, or a spectral separation on the universal input. `Proof.lean:229–232` negates that universal proposition by specializing it to m = n = 2, k = 1 and the explicit witness, discharging every dimension and rank condition. Thus the result is not a theorem about only a certificate or a separately defined one-step conjecture. Refutation at one admissible instance settles the entire original yes/no question; it does not prove failure separately at every rank. The README correctly excludes the manuscript's stronger sharp all-rank 4^r result from these Lean exports.

## Probability law, residuals and endpoints

`Definitions.lean:23–24` defines the sum of squared complex moduli. At a nonzero residual S it is positive, as follows from `Proof.lean:30–37`. `pivotMass` at definition lines 32–34 therefore assigns precisely |Sᵢⱼ|² divided by that sum to the jointly sampled pair `(i,j)`. A pair is one label in `Fin m × Fin n`; neither independent row/column sampling nor diagonal-only sampling is substituted.

The complex update at definition lines 38–41 is Sₐᵦ − SₐⱼSᵢᵦ/Sᵢⱼ, with the correct row and column orientation and no erroneous conjugation. At a zero pivot entry it returns S only to define a total function. Such a label has exactly zero mass. At S = 0, `none` has mass one and maps to the zero residual; all entry labels have zero mass and their totalized update also remains zero. At S ≠ 0 the `none` branch has zero mass. Accordingly these totalizations preserve the canonical law, including paths that reach zero early. Impossible histories cannot contribute to the finite expectation, since their joint weight contains a zero factor and all residual/error expressions remain defined.

`historyResidual` and `historyMass` at definition lines 51–63 consume the first transition and recurse on the actual updated residual. Each next probability is conditional on that residual; no independence across steps is assumed. `expectedError` at lines 67–68 sums terminal squared errors against these complete-history masses. This is a genuine finite expectation without requiring measure-theoretic machinery.

The generic proof is substantive: `Proof.lean:39–57` proves transition nonnegativity and normalization, separating S = 0 from the positive-denominator case; lines 59–85 prove all history masses nonnegative and normalized by induction and the bijection separating the first label from the tail. Lines 87–99 establish the base expectation and the conditional-expectation recurrence. These arguments include arbitrary history length and even zero dimensions, although the conjecture itself only uses positive dimensions. At k = min(m,n) the singular tail is correctly empty; k = 0 is excluded by the original target, while the auxiliary process remains well-defined there. No endpoint is silently removed to obtain the counterexample.

## Norm and spectral meanings

The explicit squared-modulus sum is exactly the requested squared Frobenius norm. `Proof.lean:24–28` additionally proves equality to Mathlib's norm squared with `Matrix.Norms.Frobenius` explicitly in scope; both Challenge and Solution use that same scope. There is no confusion with the spectral norm, an entrywise maximum norm, or the norm of an expected residual.

`Definitions.lean:72–78` uses the actual singular values of `Matrix.toEuclideanLin A`. The tail `[k, min(m,n))` converts the original one-based indices j > k correctly. I checked the pinned [Mathlib SingularValues source](https://raw.githubusercontent.com/leanprover-community/mathlib4/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/InnerProductSpace/SingularValues.lean): these are decreasing, zero-based square roots of eigenvalues of the actual adjoint composition, with zeros beyond the rank. Truncating at min(m,n) therefore agrees with the rectangular matrix convention.

In the witness proof, the spectral data are not external assumptions. `Proof.lean:119–123` verifies the Gram matrix; lines 150–170 identify the actual Euclidean adjoint composition and its characteristic polynomial. Lines 173–187 identify the decreasing eigenvalue list as [9,1] using sorted characteristic-polynomial roots, and lines 189–204 obtain the actual singular values 3 and 1 and tail 1. This chain matches the independently checkable Gram eigenvectors (1,1) and (1,−1).

## Independent exact witness calculation

I reconstructed the four outcomes using independently written Python `fractions.Fraction` arithmetic, without executing submitted code. For A = [[2,1],[1,2]], the squared Frobenius norm is 10 and AᴴA = [[5,4],[4,5]]. The four pivot results are:

| Pivot, zero-based | Probability | Residual | Squared error |
| --- | --- | --- | --- |
| (0,0) | 2/5 | [[0,0],[0,3/2]] | 9/4 |
| (0,1) | 1/10 | [[0,0],[−3,0]] | 9 |
| (1,0) | 1/10 | [[0,−3],[0,0]] | 9 |
| (1,1) | 2/5 | [[3/2,0],[0,0]] | 9/4 |

The probabilities sum to one. The expected error is 2(2/5)(9/4) + 2(1/10)9 = 18/5, while 2¹ times the rank-one tail is 2; the strict gap is 8/5. Every positive-mass second-step residual also vanishes exactly, consistent with the full-rank endpoint. `Proof.lean:125–147` derives the probability and error tables from the actual definitions and expectation recurrence, rather than assuming table entries. Lines 207–232 connect the exact scalar inequality to the witness and then to the full universal negation. No limiting argument or numerical spectral approximation is needed.

## Trust boundary and limits

The four deliberate placeholders occur only in `Challenge.lean:12,19,30,33`. Solution imports Proof, which imports the proof-independent Definitions; neither imports Challenge. Inspection found no proof-side `sorry`, custom axiom, `native_decide`, unsafe implementation, or command redefining the logical environment. The scalar LeanCert step explicitly selects kernel trust, and internal/public declarations are checked with `#assert_trust kernel` and axiom-printing commands. Comparator requests all four public targets, allows only `propext`, `Classical.choice`, and `Quot.sound`, and exposes no replaceable definition holes.

The toolchain and dependency revisions are pinned. An ordinary Git diff found Definitions, Proof, Challenge, Solution and the relevant build/comparator configuration unchanged between the README's proof revision `973f95969701601dcae7b30683b175843baa9c22` and this reviewed PR head. Source authorship and the distinction between Colbrook's mathematical counterexample and Stepaniants's AI-assisted formalization are preserved.

This review did not run Lean locally, authenticate remote CI artifacts, or claim external human peer review. The integration owner is checking those mechanical/provenance requirements separately. Two minor historical-document remnants do not affect the proof: `NUMERICAL_TARGETS.md` still has its statement-stage waiting status, and `lake-manifest.json` retains the copied project name `NLAMI19` although the actual lake configuration names `NLARA03`. Neither changes the inspected mathematical definitions, declarations or probability model.
