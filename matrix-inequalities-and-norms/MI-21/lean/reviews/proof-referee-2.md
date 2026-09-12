# MI-21 independent final proof referee 2 — PASS

**Verdict: PASS / APPROVE the complete Lean proof at the frozen mathematical hashes below.** No mathematical correction is requested. This is an independent agent proof review with fresh local re-elaboration, not external human peer review, historical-priority certification, an upstream endorsement, or a Linux Comparator result. Root controls the separate remote verification and publication stages.

Reviewer: OpenAI Codex agent `/root/leancert_examples`. I did not author the MI-21 Definitions, Challenge, numerical plan, source solution, Proof or Solution. I previously reviewed its statement boundary, then independently read the complete canonical README, complete Colbrook solution.tex, every line of the finished Proof and Solution, and the relevant pinned Mathlib definitions and theorem bodies. I made no mathematical source changes.

## Scope and fidelity

The reviewed boundary is byte-identical to both approved statement reviews. It retains every positive dimension and number of summands, arbitrary complex positive definite input families, all t in [0,1], all s,r,p>0 with sr≥1, and every unitarily invariant complex matrix norm. The weighted mean and right-hand product preserve the original noncommuting factor order and real exponents. Positive definiteness is actual `Matrix.PosDef`, and spectral powers are actual `CFC.rpow`.

The three public exports have the same signatures as the frozen Challenge. They prove generic admissibility of the chosen operator norm, the complete counterexample for every p>0, and the original universal assertion's full negation. The final contradiction chooses m=n=2, t=s=1/2, r=2 and p=1, with all parameter inequalities checked. This is a valid instantiation of the universal target, rather than a restricted replacement statement. The internal right-matrix identity holds even without p>0 because every aggregate factor is the identity; retaining the positive-p premise in the public counterexample does not hide a vacuity.

## Actual norm and unitary-invariance bridge

`operatorNorm_eq` is definitionally equal to Mathlib's L2 operator norm instance, as the fresh fully elaborated inspection explicitly shows through `Matrix.instL2OpNormedRing`. I checked `Analysis/CStarAlgebra/Matrix.lean` lines 103–116 and 254–293: `Matrix.toEuclideanCLM` is the natural star-algebra equivalence to continuous complex-linear operators on genuine Euclidean space, and the scoped matrix norm is exactly that operator norm. There is no default entrywise-norm substitution.

`operatorNorm_isUnitaryInvariant_proved` proves all five stipulated properties for every matrix dimension: nonnegativity, definiteness, triangle inequality, full complex absolute homogeneity, and invariance under two independent unitary factors. The two inverse-adjoint identities produce actual `unitary (Mat n)` membership, after which the genuine CStarRing unitary norm identities apply on the left and right. I inspected those identities in `Analysis/CStarAlgebra/Basic.lean` lines 244–261. No operator-norm-specific assumption was added to the original universal norm class.

The generic eigenvalue lower bound transports the nonzero coordinate vector to `EuclideanSpace ℂ (Fin n)` using `WithLp.toLp 2`, proves the actual `toEuclideanCLM` eigenvector equation, applies `ContinuousLinearMap.le_opNorm`, and divides only by a proved positive vector norm. The nonnegative real eigenvalue condition is established from the retained strict LeanCert gap. Thus the numeric eigenvalue is a proved lower bound on the genuine norm, not its replacement definition.

## Actual CFC mean identities

I checked the generic `geometricMean_eq_of_riccati` proof against its full premises and actual Mathlib CFC APIs. For positive definite A, the proof defines H=A^(1/2) and J=A^(-1/2), proves both HJ=I and JH=I from strict positivity, derives that the independently checked right inverse K equals A^(-1), and obtains J²=K from actual real-power addition. The positive candidate X gives a positive `J*X*J`. Its square equals `J*B*J` by the ordered Riccati equation, so genuine `CFC.sqrt_unique` identifies the square root. Congruence by H then gives the original geometric mean exactly. No covariance, geometric-mean formula, square-root selection or candidate identity is assumed as a theorem about this witness.

I inspected `CFC.sqrt_unique`, `CFC.rpow_add`, `CFC.rpow_mul_rpow_neg` and `CFC.rpow_neg_mul_rpow` in pinned `Rpow/Basic.lean` and the conjugation positivity result in `Algebra/Order/Star/Basic.lean`. Their hypotheses match the proof. The generic lemma needs no additional B-positive-definiteness premise because the proved positive candidate and square identity already justify the required CFC square root; the concrete source inputs are nonetheless independently proved positive definite.

`mean_squared_of_scaled_riccati` normalizes a positive semidefinite rational numerator N by the actual positive scalar 1/sqrt(h). The h>0 proof justifies all inverse cancellations and the square-root square identity. Applying the preceding actual mean theorem and squaring cancels the scalar root analytically, giving N²/h. The proof separately certifies both mean numerators and both actual inverses. It therefore does not rely on the source's symmetry/covariance shortcut without proof.

The four input square roots are actual CFC positive square roots of positive matrices. Positivity of C,E, involution/Hermitian symmetry of S, positive definiteness under its invertible congruence, and both aggregate identities are proved. These bridges connect every displayed rational matrix back to the actual nonlinear expressions in the full target.

## Independent numerical reconstruction

My independent Fraction script was rerun and extended to the completed proof's exact second numerator and common scaling. It checks the rational C,E,S, all four input matrices and their positive leading minors, S²=I and S=Sᵀ, and both aggregate sums I. It reconstructs D=SES and D₂=SCS, the independent parameters δ=5/3 and δ₂=3/5, and both ordinary scaled Riccati identities.

For the actual implementation's common-scale form, it independently checks

- h=61697295/8682716;
- N=[[443355,33000],[33000,605715]]/310097;
- N₂=SNS=[[506715,-85800],[-85800,542355]]/310097;
- N C⁻¹ N=hD and N₂ E⁻¹ N₂=hD₂;
- N₂=(5/3)(D₂+(3/5)E) and h=(25/9)h₂.

Both squared actual means therefore match the implementation's rational results, and their sum is exactly L=[[8216600,-985600],[-985600,11912600]]/12158163. Direct multiplication gives L(1,-4)=(1351000/1350907)(1,-4), with gap 93/1350907>0. These reconstructions supplement rather than replace the kernel-checked analytic proof.

## Kernel trust, retained LeanCert and proof quality

I independently compiled current Definitions into a fresh artifact prefix, then current Proof against that fresh Definitions artifact, then current Solution against the fresh Proof. All commands exited zero with no warnings or errors. They did not rely on an old local MI-21 proof artifact. The eight internal and three public kernel trust checks all passed, and each of the 11 fresh transitive axiom reports contains exactly `propext`, `Classical.choice`, and `Quot.sound`.

I independently inspected the elaborated proof terms against those fresh artifacts. The scalar proof uses `LeanCert.Validity.verify_strict_upper_bound_dyadic_checked` on a degenerate point interval, with explicit kernel mode. The actual lower norm bound and strict counterexample visibly retain `witness_eigenvalue_gt_one`; the final negation uses that counterexample. Thus the LeanCert computation participates in the final proof. There are no native tactics, unsafe declarations, custom axioms, admissions or theorem holes in Proof or Solution, and neither imports the Challenge. Its three deliberate placeholders remain only in the frozen comparison template.

All ten dependency package HEADs independently match their manifest pins, with clean tracked source. This check and the fresh local artifact prefix improve reproducibility but do not replace the forthcoming authoritative Linux Comparator. The local run used Lean 4.33.1 on macOS arm64 with pinned imported dependencies; no fresh Linux dependency build is claimed.

The proof uses reusable analytic helpers and only finite 2x2 exact algebra. It avoids unnecessary numerical eigenvalue lists, matrix-square-root intervals, parameter subdivision and external numerical assumptions. I applied the relevant pinned Tau Ceti correctness/faithfulness, proof-quality, scope, reuse and attribution standards within this repository's explicit MI-21 target. No unrelated project roadmap requirement was imposed.

Mathematical counterexample attribution remains Matthew J. Colbrook, University of Cambridge. Formalization credit is George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI assistance. No George email, external peer review or source-author endorsement is asserted by the reviewed formalization.

## Bound mathematical bytes

The canonical source revision is `e7252e5307781a7c897bca6cb124f6ab838f6809`.

- `NLA/MI21/Definitions.lean`: `18ebd6d65063b6e970d76b60aab6a8a8bc595189e9b8e188895030d2172f1055` (4481 bytes).
- `Challenge.lean`: `f7dd628a7635e8860dec64460bd53adfa71ca391eec763391ae1c8e58d1588b4` (1693 bytes).
- `NUMERICAL_TARGETS.md`: `4b0582a3c2da02abf7a349e4ab4af682f6b29bf7026bff21d53edff3ab216312` (6686 bytes).
- `SOURCE_MAPPING.md`: `1aa408ef570bb889a8aeddf1fca0574f59384d6ebafaa9aed217a7d31e24fed2` (3423 bytes).
- `NLA/MI21/Proof.lean`: `7db067a9cc73e3cda027e2e01d664e4b12bf5af84e8f6b3bb10d9bd4de30e9bc` (17951 bytes).
- `Solution.lean`: `a30f8dfd1103b6ba1f1aca927e7ef4a92b6fa8ae70658463cdea649378ae1a50` (2302 bytes).
- `../README.md`: `89e90aec3c05dfa59dda22af9d14f40914262cf53be88af8e2d75f156bb0cc70` (3606 bytes).
- `../solution.tex`: `ff603ec6aa8e9d8175a39202e2d51fb31f9009b76b0f5377b203986711cfc46d` (6027 bytes).

Any mathematical change requires a fresh build and affected independent review. No canonical status, permanent problem path or target was edited by this referee.

## Independent evidence

All paths below are under `reviews/proof-referee-2-evidence/`. The execution record stores exact commands and the fresh LEAN_PATH prefix; raw logs retain their real output and status. The run script and inspection source are retained for reproduction. The independent source manifest records all reviewed hashes, and dependency-check.json records each actual package revision.

- `execution.json`: `fec34f49301e19e940ad5d087cbcbb6467120cda143ff0709584b41273fa488b` (3829 bytes).
- `definitions.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0 bytes).
- `proof.log`: `7899dd3e8e15384669023e1c2de0077f20437b194b3e5bdd788e5100df9cebf1` (797 bytes).
- `solution.log`: `2edf449d7d4eb84621b1d77c376d03519139e2b0c5fc66f5c36da516c22c0895` (289 bytes).
- `inspection.log`: `6f9e62323f074770c4d31c99c48a50509c409d635361ede5f9d29db2e02e094a` (25891 bytes).
- `axioms.log`: `57cbc416145e565e9fcb7733f7971d0166307ae9332148cc8d8ad4284003e3a3` (1086 bytes).
- `reconstruct.py`: `6aea55abafb70babdde7cfe18712943fd65e783189b97bbf588536f7391025df` (2807 bytes).
- `numerical-reconstruction.json`: `a9191a4b62abca95393872c204246cfdad6c4c20076b7d2d26ca2aecf9199ac9` (2749 bytes).
- `dependency-check.json`: `fe9da8192699844fe8bfd468be35e52d00b48e670c25f418d70addfcf7fa0a7d` (2135 bytes).
- `review-source-manifest.json`: `f5926a53f77301ac2cea22820b7924b8a6ee7709bee8d4fadf2751280f316b33` (2105 bytes).
- `run-fresh-elaboration.py`: `da3bdaab7f69d69cc52db6324eb62e8881251e7d72018f24e6641acd07a9aee3` (1726 bytes).
- `Inspect.lean`: `6feaaf35c92f996f6b0b424e169ad46d20b413418fbc82bfbed3912c562175f5` (654 bytes).
