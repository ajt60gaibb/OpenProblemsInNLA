# PR 186 bounded independent cross-review

**Verdict: PASS for MI-16, MI-20, and MI-27 in their expressly stated scopes. No mathematical or PDF blocker found.**

Reviewed exact PR 186 head `fc83d2959723c92967a26777e5238404804c848c` in `/private/tmp/nla-audit-186`. This review read all three actual `result.md` proofs and the four canonical README diffs against the published base. It did not rely on the submitted review reports. The coordinating reviewer separately audited MI-15's complete SOS proof and exact certificates; this cross-review does not claim to repeat that work or its tests. No PR 186 tests were rerun, no source or GitHub state was changed, and PDF renders were written only under `/private/tmp/nla-pdf-crossreview`.

## MI-16: symmetric multiaffine optimization and exceptional spectra

The proof in `references/holden-matrix-2026-09-12/MI-16/result.md:43–95` is valid over the full complex unitary orbit and for every nonnegative alpha,beta.

Every matrix in this spectral class is `beta I + (alpha-beta) uu*`. Expanding the permanent cancels all complex phases on the selected permutation support and gives the stated real symmetric multiaffine polynomial on the simplex. All simplex points are realized.

The minimum-support maximizer argument at lines 71–79 is sound. A maximizer exists by compactness, and its support size has a minimum among the finite possible sizes. Holding two positive coordinates' sum fixed gives `C+As+Bxy`. Negative B contradicts global maximality by moving to the boundary; zero B contradicts the chosen minimum support; positive B forces the pair equal. This does not require nonnegative coefficients and therefore applies unchanged when alpha<beta. It establishes existence of an equal-positive-coordinate maximizer, rather than asserting every maximizer has that property.

The resulting finite maximum over support sizes is explicit and the given matrices have the required spectrum. When alpha>=beta the elementary-symmetric contributions are nondecreasing with support size, justifying k=n. When beta=0 only the j=n term can survive, giving `n! alpha^n/n^n` (and zero for the all-zero spectrum); the stated zero-exponent convention handles n=1 and all endpoints. Alpha=beta yields beta^n. The example `(0,1,1)` correctly gives candidate values `0,1/2,4/9`. No arbitrary-spectrum conclusion follows or is claimed.

## MI-20: projective reductions, all summands, and singular matrices

The complete proof in `references/holden-matrix-2026-09-12/MI-20/result.md` is valid. The positive dual formulation matches [Qiu, Proposition 3.1](https://arxiv.org/html/2608.17565v2), including complex matrices and `1<p<infinity`; its attribution as known is accurate. The accompanying self-contained polar/trace-duality argument also checks out.

For the binary reduction, positivity and `X<=S` imply X vanishes on ker S, including the off-diagonal blocks. Thus conjugating by the inverse square root on the support is legitimate. The objective is convex on the complete positive contraction interval, and spectral decomposition expresses a contraction as a convex combination of nested projections and zero. With S,R fixed, at least one projection attains an objective at least as large. No fixed rank is inferred.

For the all-m dilation (lines 62–102), each Xi is supported on S. Adding identity to K1 on ker S and zero to the other Kj makes their sum exactly the identity on the entire original space. Consequently `W*W=I`, even if S is singular and R has support outside range(S). The coordinate projections are mutually orthogonal and sum to the identity on dimension mn. The positive square-root identity for `WSW*` follows by squaring `W S^(1/2) W*` and checking positivity. Therefore each new modulus is `W Xi W*`, and its product with the embedded R is `W R Xi W*`. All relevant Schatten norms are preserved because an isometric embedding adds only zero singular values. This holds for arbitrary complex entries and singular S,R. The number of summands stays m; the dimension increases to mn. The reverse inclusion gives equality only of the dimension-free suprema, exactly as stated. The monotonicity and tensor-product consistency relations are valid and do not determine the desired constant.

## MI-27: variable trace, entropy concavity, and sharpness

Both theorems in `references/holden-matrix-2026-09-12/MI-27/result.md` pass.

For the forward projection implication (lines 35–45), the eigenvalues of the regularized contraction lie strictly between zero and one, so both A and B remain positive definite with their sum fixed. Sending epsilon to zero is harmless because S and log S remain fixed and binary entropy is continuous at both endpoints.

For the reverse implication (lines 47–69), the nested-projection coefficients are nonnegative and total one after including the zero projection. The component traces are allowed to differ. Linearity followed by trace-norm convexity and entropy concavity gives the inequality with the original trace b; the Jensen inequality points in the correct direction. The proof never assumes projections are extreme points of a fixed weighted-trace slice. This explicitly resolves the delicate trace-slice issue and works in all dimensions over the complex field.

For the sharpness family (lines 77–126), `S_t^(1/2) P S_t^(1/2)=t(1-t) J_2`. The regularized contraction has eigenvalues `t^2` and `1-t^2`, proving strict positive definiteness of both A_t and B_t for the entire stated parameter interval. The skew commutator has two equal singular values, so its trace norm contains the correct factor two. `b_t/(2t)->1`, the numerator is asymptotic to `2t log(1/t)`, and entropy at b_t has the same asymptotic. The ratio tends to one. Hence every universal coefficient below one fails on strictly admissible inputs. The universal coefficient-one upper bound remains unproved, as the publication says.

## Publication scope and permanent targets

The four canonical README diffs preserve the original mathematical statements and existing IDs/paths. MI-15 remains **Partially resolved**, and MI-16 changes to **Partially resolved** only for its restricted spectral class. MI-20 and MI-27 remain **Open**. The new RESOLVED.md text explicitly distinguishes the limited results, keeps the open-target count unchanged, and asserts neither a full solution nor historical novelty nor formal/external-human verification. This is consistent with the proofs reviewed here. No change to any mathematical target was found.

## PDF disposition

Used the PDF skill, Poppler `pdftoppm` at 85 dpi, and complete-page contact sheets. **All 41 pages of the following eight PDFs were visually inspected.** Source statements and equations had already been read in full in the mathematical audits. Inspection found no clipped equations, overlapping text, broken tables, missing mathematical glyphs, misleading status labels, or incomplete references. Some canonical entries retain short continuation pages; their content is intact and this is not a defect requiring a change.

| PDF | Pages inspected | Disposition |
| --- | --- | --- |
| `/private/tmp/nla-audit-186/matrix-inequalities-and-norms/MI-15/problem.pdf` | 1–2 | PASS; partial status and orders 8–12 explicitly retained |
| `/private/tmp/nla-audit-186/matrix-inequalities-and-norms/MI-16/problem.pdf` | 1–2 | PASS; restricted-spectrum formula and remaining arbitrary-spectrum target clear |
| `/private/tmp/nla-audit-186/matrix-inequalities-and-norms/MI-20/problem.pdf` | 1 | PASS; Open status and dimension-free target legible |
| `/private/tmp/nla-audit-186/matrix-inequalities-and-norms/MI-27/problem.pdf` | 1–2 | PASS; Open status and coefficient-one target legible |
| `/private/tmp/nla-audit-191/randomized-and-low-rank-approximation/RA-04/problem.pdf` | 1–3 | PASS; original conjecture, extra logarithmic term, and partial regimes intact |
| `/private/tmp/nla-audit-190/randomized-and-low-rank-approximation/RA-14/problem.pdf` | 1–2 | PASS; oracle model and polynomial dimension restriction intact |
| `/private/tmp/nla-audit-191/references/holden-ra04-2026-09-12/RA04_partial_results.pdf` | 1–16 | PASS; all proof, table, source, and remaining-obligation pages inspected |
| `/private/tmp/nla-audit-190/references/holden-ra14-2026-09-12/package/report.pdf` | 1–13 | PASS; all proof, query accounting, experiment, source, and scope pages inspected |

Rendering inventory and page counts: `/private/tmp/nla-pdf-crossreview/manifest.json`. Full-page PNGs, contact sheets, and extracted text are retained in that scratch directory. PDFs were neither edited nor re-exported. These are visual and informal analytic checks, not proof-assistant verification.
