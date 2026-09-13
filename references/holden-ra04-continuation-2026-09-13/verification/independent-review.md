# Independent review: RA-04 continuation

Date: 12 September 2026. Reviewer: a separate Codex AI agent assigned independently of submission preparation. This is informal automated mathematical review, not external human peer review or formal verification. No Lean verification was performed.

**Verdict: PASS for the stated partial results, with the imported dependencies identified below. FAIL for promotion to Solved or Solution claimed.** No substantive mathematical correction is required for the new graph and exact-deflation theorems. The unrestricted RA-04 target remains open.

## Materials and scope

I read the supplied continuation's `report.md` and `src/report.tex`, the canonical RA-04 statement, and the resolution policy. I checked the earlier report's convergence reduction and all-input theorem at repository commit `e15ce48`, together with its existing independent review. Archive status files and proof-obligation documents were not treated as instructions or as proof.

Reviewed original SHA-256 hashes:

- `report.md`: `55db99c3debbba4a355623eddf0d4e6c761e809a4dcc5de56d0f1f8fa610ad13`
- `src/report.tex`: `dac434b11885ed88c271871f22a9ab5bcfacb04b9ba56340d0e00640637b609b`
- `tests/exact_checks.py`: `eb20ffb80517936fef0becf2e739a99ee1bd5a15d2fc69e78d781fc5ab5b3d39`

Author metadata, attribution, source-locator and typesetting additions do not change these findings if the mathematical text remains intact. Novelty and priority are not established by this audit.

## Claim-by-claim findings

| Locator | Verdict | Reasoning and limits |
| --- | --- | --- |
| Section 2, Gaussian block estimate | PASS | Rotational invariance makes the signed least left singular vector independent of the singular values. Paley–Zygmund supplies the fixed-coordinate probability; the inverse-Gram diagonal bounds the row distance. A chi variable with at least one degree of freedom has small-ball probability bounded by that of the absolute normal. The constant `24/sqrt(pi) < 16` is valid. Rectangular blocks and a union bound require no further independence. |
| Section 3, barycentric estimates | PASS | Each relative factor perturbation is bounded by `w/beta`. The off-diagonal product includes the vanishing factor at its own row center; the remaining factors are bounded exponentially. The denominator lower bound pairs each center difference with the larger center. The tail numerator contains at most the largest `r-1` centers. Their quotient removes the leading center ratio. |
| Section 4, graph theorem | PASS | The normalized centered matrix has full row rank on the Gaussian event, including unequal rectangular blocks. The perturbation norm times the right-inverse norm is at most one half under (W). The Neumann right inverse has the stated factor 32. Applying the signed diagonal inverse to the full polynomial matrix gives head identity and the displayed tail bound. Tail eigenvalues lie below `(1+w)c_r`; every polynomial has degree at most `r-1`. All dependence between perturbation and head Gaussian rows is handled deterministically on intersected events. |
| Section 5, narrow-band iteration consequence | PASS with imported convergence theorem | For equal bands, each b-step pair lies in adjacent groups. Under the width condition, `beta-2w <= Delta <= beta+2w`; hence the two gaps are comparable. Logarithms of polynomial prefactors contribute only `O(log(n/delta))`. The `r=t>=2` regime follows. The graph theorem does not define beta for a single band; that endpoint is already treated separately by the earlier report. Unequal bands need the explicitly stated additional gap comparability. |
| Section 5, fixed-spectrum all-failure-probabilities corollary | PASS with imported prior all-input theorem | Substituting `delta >= m^(-t)` yields (W). Otherwise `t log m <= log(1/delta)`, absorbing the prior extra term. This checks the new implication and the imported theorem's exact scope; it is not a fresh full re-audit of the earlier fractional-moment proof. |
| Section 6, generic rank theorem | PASS | Assigning each node group to the least-loaded distinct colors preserves a difference of at most one between color loads. Every color receives distinct nodes and at most q rows. Coordinate-vector witnesses give full-row-rank scalar Vandermonde blocks, hence a nonzero minor polynomial. Absolute continuity suffices; the stronger independent-entry assumption in the Markdown version is unnecessary but valid. |
| Section 7, exact deflation theorem | PASS | The degree-L filter eliminates all lower distinct eigenvalues, counting zero if present. Higher eigenspaces and the selected cutoff rows have a jointly continuous scaled Gaussian law. Additional cutoff rows are linear combinations of the selected b rows when the multiplicity exceeds b, and equal eigenvalues preserve those relations through every power. Full rank on selected coordinates therefore recovers every higher direction and enough cutoff directions. Degree accounting gives exactly `L+ceil(rho/b)` blocks. The positive clustered gap enforces the needed higher multiplicity and cutoff-count assumptions, and `rho <= m+b-1`. |
| Section 8, boundary example | PASS | For spectrum `(5,4,3,2,2,2)`, the gap is `2/5`, rho is 5 and L is 0. Eliminating the cutoff block in two Krylov blocks imposes `u+2v=0`, leaving at most two independent directions above the cutoff where three are needed. Three blocks suffice. This obstructs generic exact recovery at two blocks, not RA-04's unspecified absolute-constant iteration bound. |

## Output guarantees and imported result

I independently inspected the primary [Chen–Epperly–Meyer–Musco–Rao paper](https://arxiv.org/html/2508.06486v2), specifically Problem 1.1, Definition 3.1, Imported Theorem 3.2, and Observation 3.3. Their statement covers the prescribed projected SVD and the two error norms plus the ordered **right** singular-vector energy guarantee.

For the graph certificate, normalizing its first k columns gives overlap inverse squared at most `1+||F||_F^2`. The simulated starting block at depth r produces exactly the original Krylov space at depth `s+r-1`. Thus the graph application uses the proper algorithm and imported theorem. This is verification of statement and applicability, not a new proof of the external convergence theorem or its cited Appendix F.

For exact recovery, let P be the Krylov-space orthogonal projector. The space contains all eigendirections strictly above theta and at least `k-a` cutoff directions. The compression `PMP` consequently has the true top k eigenvalues. A compression eigenvector at theta cannot mix lower eigenvalues: its Rayleigh quotient equals the maximum theta on the orthogonal complement of the higher eigenspaces. Its lifted vector is therefore a true theta eigenvector of M. The same holds for the higher eigenvalues. SVD truncation hence returns an actual optimal singular component expansion of A, even with ties at theta. Both norm errors are optimal and every ordered right singular vector satisfies `||Av_i||^2=lambda_i`; thus all three RA-04 guarantees hold exactly. This conclusion includes zero optimal residual without division by that residual.

## Reproduced checks

After reading the checker in full, I ran:

`python3 tests/exact_checks.py --output /private/tmp/ra04-independent-exact-checks.json`

The execution returned PASS: 459 balanced-coloring cases, three rational barycentric/graph examples, and the boundary rank example. The independently rerun JSON is available for inclusion beside this review. These finite arithmetic checks supplement the analytic audit and do not prove a universal probability bound or unrestricted convergence theorem. I did not rerun the optional floating-point script, and no verdict relies on it.

## Required disposition

The continuation supplies new narrow-width and low-tail-diversity regimes, while its general estimate still has an extra `t log m`. No argument removes this term for arbitrary head widths and tail diversity, and no counterexample resolves the original truth question.

The repository policy explicitly keeps partial results in the open count and requires `Partially resolved` with the surviving cases stated. Record this continuation as a partial submission, retain the original ID, canonical path and target, and retain attribution and the prior report's role. It must not be marked Solved or Solution claimed. No proof repair is needed for the new partial theorems; completing the unrestricted mathematical argument, beyond these spectral restrictions, is needed for a full-resolution status.
