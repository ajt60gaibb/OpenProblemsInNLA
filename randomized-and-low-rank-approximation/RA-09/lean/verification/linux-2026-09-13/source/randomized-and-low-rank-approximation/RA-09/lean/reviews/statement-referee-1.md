# RA-09 independent statement referee 1

**Verdict: APPROVE these exact statements for implementation.** The 17 contracts retain the complete original affirmative Frobenius transfer target. No mathematical boundary correction is requested. This is a statement review, not a proof of those contracts or a Lean-verified status recommendation.

Reviewer: `/root`, an OpenAI Codex AI agent. I did not write the RA-09 statement package or an RA-09 implementation. I previously contributed generic proof helpers to the separate RA-08 project and discussed the campaign's pure-algebra verification scope; those roles are disclosed and do not supply an RA-09 proof. Any later RA-09 implementation contribution would disqualify me as an independent final proof referee. This is not human peer review or official Tau Ceti endorsement.

## Frozen inputs and independent checks

The approved freeze is `reviews/statement-freeze.json`, SHA-256 `c144b68990fca06c554790b25bfaef7544c0a8baf532e5b38365fe74ee9c87ed`: **31 project inputs and 17 original source/policy Git files** at base `5830ed4fb06da0659414a3deb2a40ad327aca052`. All were rehashed before and after my fresh checks; original bytes match the actual Git blobs. The later handoff has SHA-256 `5ecf95acfe00db1e19165cfaa9f3ed78a097e653570664bcb47b3ee6542d118d`.

| Boundary | SHA-256 |
| --- | --- |
| Definitions | `2a9b0d9d536bc2620fbe3814ed95640caeae8a49e8b13a9e2136b469ba09ece9` |
| Challenge | `5b275a09558f3b03b67b4ef0c7764db854d9c516190f05135a426c14eb7b1e6e` |
| Numerical/mathematical plan | `638e5a3c5c87bc284eee127ac11dde58fba9d9c705e40669efcd1dcb91ed52ee` |
| Source correspondence | `142f0b485aa77978ab89def0263b6456e30b660235ae635af99409c19038821a` |
| Comparator configuration | `dc16c0577badd3cefa27669c7efd3bdf525a21e5f45516e8b1f2d32158cca6cd` |

I read the complete canonical page, the complete reviewed Frobenius manuscript (including the unordered theorem, sharpness and degenerate cases), its full preamble and independent informal review, the feasibility note, all actual definitions and Challenge signatures, numerical plan and source correspondence. I inspected the relevant pinned matrix norm, order, PSD, spectral, CFC and concavity APIs. The existing campaign review protocol and its pinned Tau Ceti adaptation govern this review; no official review service is claimed.

My own fresh private prefix compiled Definitions in **16.22 s**, Challenge in **3.45 s**, and an independent actual-instance inspector in **5.88 s**. All three commands passed. The inspector imports Definitions and LeanCert verification tooling, not Challenge or an implementation. All **17 structural kernel/axiom inspections** contain exactly `propext`, `Classical.choice` and `Quot.sound`. These concern the definitions, not proofs of the 17 Challenge obligations. Challenge emitted exactly its 17 intentional admission warnings; the other commands had no warnings.

The ten exact pinned clean MI-22 dependency source/object directories were used read-only. All project objects began absent from this independent prefix; no old RA-09 or MI-22 project object was imported. No Lake invocation, dependency copy/download/rebuild, Linux or Comparator run occurred. The evidence retains the commands, source snapshots, full actual output, before/after integrity and dependency pins. No implementation or Solution exists at this review.

## Complete target and actual semantics

The final proposition quantifies over every `n≥2`, `1≤k<n`, every real symmetric PSD pair `Ahat≤A`, every continuous nonnegative nondecreasing concave function on the nonnegative half-line, every permitted ordered orthonormal decomposition of both matrices, and every `epsilon≥0`. The premise remains exactly the **difference of squared norms**:

`FSq A − FSq (truncation dHat k) ≤ (1+epsilon) FSq(A−truncation dA k)`.

The conclusion is the required relative squared Frobenius error of the actual function truncation. The weaker ordinary residual premise proved in the manuscript is not substituted into the final conjecture. The trace-deficit reduction explicitly requires the true identity and nonnegative cross trace, without assuming commutation or the converse implication.

The actual elaborated `frobeniusNorm` uses `Matrix.frobeniusNormedAddCommGroup`, as shown by the full printed definition. Its scope ends before the CFC definition. The actual elaborated functional calculus calls Mathlib's `@cfc` with the matrix topology and self-adjoint predicate; it is not a defined spectral sum. `PosSemidef` is Hermitian symmetry plus nonnegativity of the real quadratic form, and the matrix order is PSD order of the difference. The Frobenius sum/norm/trace bridge remains an explicit proof obligation, including rectangular and empty auxiliary matrices.

Ordered data use a genuine orthogonal matrix, antitone nonnegative eigenvalues, and reconstruction of the actual input. The existence contract covers every real PSD input, preventing a vacuous all-basis target. The separate semantics contract requires actual orthonormal columns and eigenvector equations. Repeated eigenvalues and zero-dimensional auxiliary cases remain allowed.

Both truncations use the **same caller-selected basis**. The function truncation discards entries as zero even when `f(0)>0`; it is not the full function of the truncated matrix. The CFC contract requires equality with every selected decomposition and independence of extensions below zero. Continuity, concavity, monotonicity and nonnegativity are required only on the original half-line. There is no zero-at-zero, operator-monotone, commuting, analytic or preferred-basis restriction.

## All 17 obligations and boundaries

The two Frobenius contracts supply the actual norm, absolute-entry sum, trace, faithfulness and left/right orthogonal invariance. The three spectral/CFC contracts supply genuine existence, every selected basis and actual functional calculus. Truncation semantics supplies PSD order, both exact tails and the zero-tail characterization. These are conclusions to be proved, not numerical assumptions supplied to the final theorem.

The scalar consequences are correctly stated for every original admissible function: the positive-argument ratio decreases, the scale has the stated signs, the below/above-cutoff inequalities and the one-sided difference bound hold, and `f(tau)=0` forces vanishing on the entire half-line. That last case remains included in positive-tail transfer; `f(tau)>0` restricts only the scalar normalization lemma where division requires it.

The branch certificate covers unbounded `d≥1,z>0` and all boundaries `z=1`, `z=d`, `d=1`. Its exact sum-of-squares identity makes the first quadratic strictly positive; the other factors have their indicated nonnegative signs. The **full ordered scalar inequality** is separately required from actual admissibility, so normalized polynomial identities alone cannot discharge the matrix theorem.

The harmonic contract starts from actual PSD of `diag(a)−b vvᵀ` and proves both zero-coordinate support and the bound `b sum(v_i²/a_i)≤1`. Total real division at zero is controlled by the support conclusion. The actual overlap weights are squared entries of the actual orthogonal change of basis; their normalization, restricted row sums, support and harmonic bounds are consequences of matrix order. No projector, pseudoinverse, eigenvalue estimate or desired matrix inequality is supplied as a premise.

Both error expansions include the actual matrices and every selected zero eigenvalue. The zero-column contract explicitly retains `f(0)`. Positive-tail transfer must prove the excess bound and the tail-scaling inequality. The zero-tail contract uses the original trace-deficit premise to require `A=Ahat_k=Ahat` and gives both actual function errors as `(n−k)f(0)²`, while allowing different null-space bases. It does not divide by the zero cutoff or assert equality of the different function truncations.

The final unconditional theorem has none of these intermediate inequalities as an external premise. No Eckart–Young theorem is needed to pass from the stated excess/tail inequalities to the relative conclusion; nonnegative epsilon and the actual exact tail identities suffice. The source's larger subhomogeneous class, unordered factor two, optimality and complex extension are outside the exports without weakening the canonical real ordered target.

## Independent exact diagnostics and proof obligations

My independent standard-library Fraction/sparse-polynomial script imports no submitted checker. It verifies the complete SOS coefficient identity and all three branch identities after multiplication by the positive denominator `z`. This is exact coefficient comparison; the necessary signs follow from the displayed factors and domain. It is not a proof of the full function-dependent scalar inequality.

A noncommuting example uses `A=diag(5,3,1)`, `B=vvᵀ` for `v=(3/5,4/5,0)`, rank one and `f(x)=x+1`. Here `A≥I≥B`. The actual trace deficit is 34, residual `714/25`, cross trace `68/25`, transformed error `1028/25`, and function tail 20. The original premise holds at `epsilon=12/5`; the transformed conclusion holds. The selected function truncation differs from full `f(B)`, exposing the positive-intercept convention.

For `A=Ahat=diag(2,0,0)`, rank two and the same function, choosing the second selected vector either as the second coordinate or as `(0,3/5,4/5)` gives different function truncations. Both exact errors equal one, namely `(n−k)f(0)²`. A separate diagonal harmonic example includes an actual zero coordinate and verifies the direct test identity `H−bH²` exactly. These finite examples check boundary interpretation; they do not replace any universal Lean proof.

Computation is appropriately minimized: the plan uses universal exact scalar algebra and finite matrix identities, with no interval subdivision or artificial numerical singleton. LeanCert kernel trust/dependency checks are the approved applicable tooling. Every actual CFC/norm/order/overlap bridge must still be proved, and the final implementation requires separate independent proof reviews and real Linux Comparator/default-kernel/control execution.

Attribution is correct: Matthew J. Colbrook retains the mathematical theorem, Persson–Meyer–Musco retain the question, and George Stepaniants receives AI-assisted formalization credit with Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, without an email. Structural adaptations from the campaign, Schiffer and Forsythe are disclosed. No source author endorsement or priority is claimed.

**One exact statement approval is given here. A second independent statement approval and coordinator gate are still required before implementation.** The permanent ID, canonical path, original target and Solved status remain unchanged. Metadata, final proof review, actual Linux and publication acceptance remain future gates.
