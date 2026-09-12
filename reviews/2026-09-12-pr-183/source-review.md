# Independent PR 183 MI-22 Lean source audit

**Verdict: PASS for the actual proof and full English-to-Lean target fidelity. No mathematical or proof-source blocker found.**

Reviewer: Codex AI agent `/root/audit_spectral_linear`, 12 September 2026. Exact reviewed head: `1dddf3d17681a91adbcf1dfa43b7ee79653f55fd`, read-only worktree `/private/tmp/nla-audit-183`. This is an independent source and mathematical audit, not external human peer review and not a claimed local Lean build. Current authenticated Linux/Comparator evidence and canonical PDF publication are separately assigned to the coordinating reviewers. Submitted review verdicts were not used as proof evidence.

Paths below are relative to `matrix-inequalities-and-norms/MI-22/lean/` unless specified. I read the entire actual Definitions, FunctionalCalculus, Norms, SingularValues, Witness, ExactData, Proof, Challenge and Solution modules, the configuration, original canonical statement, and disclosed source correspondence. A second independent agent cross-checked the singular-value/norm bridge.

## Exact original target

`NLA/MI22/Definitions.lean:24–60` faithfully retains complex matrices of every positive dimension, both positive-definite hypotheses, every real `t` in the closed interval `[0,1]`, and the original noncommuting factor order in the geometric mean and `A^t(A#_t B)B^(1-t)`. `singularPrefix` uses indices `0,…,k−1`, exactly the original `s_1,…,s_k`; `SingularLogMajorized` includes every proper prefix and **equality**, not inequality, at the full product. There is no commutation, rank, rounding, root-certificate or spectral-list assumption. The positive-definite canonical target is a subcase of the primary paper's semidefinite target, so this positive-definite counterexample also refutes the broader statement.

The retained canonical `Problem statement` and all following source notes are exactly unchanged from main `f41f1f9ffa2171550d4bb795862c6170c4f26070`. I independently checked the primary preprint: printed pp. 1–2 define actual descending singular values, full log-majorization and the weighted mean; p. 3, Conjecture 1.1 is the displayed target. It is distinct from Conjecture 1.2. [Ghabries–Abbas–Mourad–Assi primary preprint](https://arxiv.org/pdf/2105.13356).

## Actual analytic and spectral bridges

- **Genuine powers:** `Definitions.lean:28` is `CFC.rpow`, and `FunctionalCalculus.lean:24–67` proves strict positivity, natural powers, the addition/composition laws and unitary spectral representation. I read the pinned upstream Mathlib `Rpow/Basic.lean` at `0df444a360eaa60ab8c11dca51a86af692955474`: `rpow_eq_cfc_real` (line 418), `rpow_natCast` (449), `rpow_add` (459), `rpow_rpow` (469) and `IsStrictlyPositive.rpow` (752). All actual uses supply positivity/invertibility and the required nonzero first exponent. `Matrix.IsHermitian.cfc_eq` in the same pinned HermitianFunctionalCalculus source (lines 127–149) works on the finite spectrum, so the arbitrary-real-exponent representation does not smuggle in global continuity at zero. Positive eigenvalues are the intended principal-power domain. [Pinned CFC power source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean).
- **Actual singular values and norms:** `Definitions.lean:42–69` uses Mathlib's singular values of the actual Euclidean linear map, the actual induced Euclidean CLM norm, and the sum of all squared complex entry moduli. `SingularValues.lean:19–62` identifies the top PSD eigenvalue with the operator norm, proves `toEuclideanLin(AᴴA)=adjoint(A)∘A`, and derives the first singular value from its square and nonnegativity. Lines 64–78 retain descending order, all eigenvalue multiplicities and zero extension beyond dimension. Nothing replaces spectra by a user-supplied list or a distinct-eigenvalue maximum.
- **Frobenius/action/power bounds:** `Norms.lean:20–86` explicitly fixes the L2 matrix norm, uses unitary invariance and the full finite eigenfamily, proves `trace(AᴴA).re=∑|a_ij|²`, and derives both `||A||₂²≤||A||_F²` and the coordinate action bound. The eighth-power norm identity is applied only to a Hermitian matrix. The first-singular-value bridge requires `n≥1`; general norm/Frobenius statements also make sense at dimension zero and do not create an empty-index maximum loophole.

## Independently reconstructed rational witness and complete proof

The adapted witness is explicit in `Definitions.lean:71–117`: `D=diag(16,1/16,1)`, `A=D²`,

`T = [[4616,-39,-1250],[-39,55069,-1519],[-1250,-1519,6499]] / 8192`,

`B=D T^8 D`, and the genuine Euclidean unit vector `x=(0,4/5,-3/5)`.

I independently recomputed the matrix arithmetic using Python's standard-library `Fraction`, without running or importing contributor code. The exact LDL factorization has determinant-one lower factor and strictly positive pivots `577/1024`, `254196983/37814272`, and `1555181999141/2082381684736`. It therefore proves actual Hermitian positive definiteness of `T`; powers and invertible congruence prove `A,B>0`. Every one of the **48 actual rational table entries** in `ExactData.lean:22–48` matches fresh multiplication (`T²`, `T⁴`, `T⁸`, `B`, `AB`, and the first row of `N`). The table identities are themselves proved by `norm_num` in lines 50–118, never assumed as premises.

The exact fractions verify the strict comparisons below (decimals only summarize the exact rational calculations):

| Quantity | Independently reconstructed value | Needed comparison |
| --- | --- | --- |
| `trace(B)` | approximately 20497.893149837477 | `< 4^8 = 65536` |
| `(Nx)_0` | approximately 45616.01572367239 | `> 44000` |
| `||AB||_F²` | approximately 105373743.6850374 | `< 10500² = 110250000` |

Exact results and margins are retained outside the repository in `/private/tmp/nla-pr183-independent-fractions.json`.

`Witness.lean:63–167` proves the principal powers of A, the normalized inner root `(D⁻¹BD⁻¹)^(1/8)=T`, and the weighted mean, using actual CFC throughout. For the **actual** `Y=B^(1/8)`, it proves `Y>0`, `Y^8=B`, `B^(7/8)Y=B`, and the order-sensitive identity

`L Y = N = A^(5/8) T D B`, where `L=A^(1/8)(A#_(1/8)B)B^(7/8)`.

Thus `||Y||₂^8=||B||₂≤trace(B)<4^8` gives `||Y||₂<4`. The genuine coordinate/action and submultiplicativity bounds give

`44000 < (Nx)_0 ≤ ||N||₂ ≤ ||L||₂ ||Y||₂`,

hence `||L||₂>11000`, while the Frobenius comparison gives `||AB||₂<10500`. These are the exact arguments in `Proof.lean:37–84`; no approximate-root residual or floating-point eigenvalue inference is required.

`Proof.lean:91–116` transfers this to the strict **actual** first-singular-value reversal and contradicts the `k=1<n=3` conjunct. Instantiating the universal target at `n=3,t=1/8` proves its complete negation. It is correct to refute the whole conjunction with one proper-prefix violation; proving or disproving its full-product equality separately is unnecessary. The theorem does not claim failure at every t or classify surviving ranges.

## Authorship and trust boundary

Canonical README lines 16–28 preserve Matthew J. Colbrook's original negative-resolution/method credit and Cambridge affiliation, while giving George Stepaniants the disclosed adaptation/formalization credit and Caltech affiliation with AI assistance. The altered witness and 11000/10500 thresholds are explicit. I parsed the original R in `../solution.tex:128–135` and independently checked that each T entry is its exact nearest multiple of `1/8192`. The original integer B, its residual-to-root theorem, and its 10900/10200 bounds are correctly distinguished as source results not formalized by this witness. That adaptation still settles the identical universal target.

The only Challenge admissions are its eight intentional statement-boundary placeholders. `Solution.lean:5` imports `NLA.MI22.Proof`, not Challenge; all eight public declarations (lines 15–90) are proved from the corresponding completed declarations with unchanged statements. The proof import closure contains no `sorry`, unproved axiom, unsafe/native proof mechanism, custom command or surrogate definition. `Proof.lean:16,86–89` fixes LeanCert trust to kernel and uses it only for the retained scalar comparison `10500<11000`; the actual matrix, root and norm work is proved separately. This scalar fact is consumed in lines 102–103. The comparator names all eight exports and permits only the three standard axioms. `lakefile.toml` retains Challenge as the default target but also declares Solution, so a default-only build would not be sufficient; the separate assigned CI audit must authenticate the actual Solution/Comparator/kernel execution.

**Limits:** I did not rerun Lean or authenticate the remote workflow in this source-only assignment, and I do not infer a build result merely from the submitted labels or `#print axioms` commands. Promotion requires the independently authenticated Linux evidence handled by the other reviewers. Subject to that separate operational gate, the actual target and complete mathematical proof pass this audit.

Companion independent bridge review: `/private/tmp/nla-pr183-norm-crosscheck.md` (Codex AI agent `/root/audit_spectral_linear/ie16_pr178`, same exact head), final PASS. It additionally checked the pinned Mathlib Euclidean-matrix, adjoint, spectrum and singular-value API definitions, including repeated eigenvalues and zero-rank/zero-dimension conventions.
