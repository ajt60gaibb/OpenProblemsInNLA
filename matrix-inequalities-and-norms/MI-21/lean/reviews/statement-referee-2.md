# MI-21 independent statement referee 2 — APPROVE

**Verdict: APPROVE the frozen statement boundary for proof implementation.** No mathematical correction is requested. This is a statement/fidelity review, not an approval of a completed Lean proof, a Linux Comparator result, or a catalog-status change. No Proof.lean or Solution.lean existed when this report was frozen.

Reviewer: OpenAI Codex agent `/root/leancert_examples`. I did not author the MI-21 definitions, Challenge, numerical plan or source solution. I read the complete canonical README and the complete Colbrook solution.tex, inspected the actual Definitions and all three Challenge exports, independently re-elaborated the statements into fresh local artifacts, and reconstructed the numerical witness from rational arithmetic independently of the draft's saved calculations.

## Reviewed boundary and sources

The authoritative repository base is `e7252e5307781a7c897bca6cb124f6ab838f6809`. The source is MI-21's retained canonical target and Matthew J. Colbrook's complete Theorem 1.1 and proof. The following SHA-256 values bind this approval:

- `NLA/MI21/Definitions.lean`: `18ebd6d65063b6e970d76b60aab6a8a8bc595189e9b8e188895030d2172f1055` (4481 bytes).
- `Challenge.lean`: `f7dd628a7635e8860dec64460bd53adfa71ca391eec763391ae1c8e58d1588b4` (1693 bytes).
- `NUMERICAL_TARGETS.md`: `4b0582a3c2da02abf7a349e4ab4af682f6b29bf7026bff21d53edff3ab216312` (6686 bytes).
- `SOURCE_MAPPING.md`: `1aa408ef570bb889a8aeddf1fca0574f59384d6ebafaa9aed217a7d31e24fed2` (3423 bytes).
- `../README.md`: `89e90aec3c05dfa59dda22af9d14f40914262cf53be88af8e2d75f156bb0cc70` (3606 bytes).
- `../solution.tex`: `ff603ec6aa8e9d8175a39202e2d51fb31f9009b76b0f5377b203986711cfc46d` (6027 bytes).

Any change to the mathematical content of Definitions, Challenge or NUMERICAL_TARGETS requires renewed statement review. No independent human review, historical priority or source-author endorsement is claimed here.

## Complete target fidelity

I checked each source quantifier and factor order adversarially. `GeometricMeanNormConjecture` quantifies over every positive number m of summands and positive matrix order n, every two complex matrix families indexed by Fin m, positive definiteness of every actual summand, every t in the closed interval [0,1], every s,r,p>0 with 1≤s*r, and every unitarily invariant norm. The final inequality's direction is the original left≤right direction. There is no added commutation, real-only, simultaneous-diagonalization, uniform-spectrum, invertibility-certificate, or precomputed-output hypothesis.

The left expression is the sum of the real r-th powers of the weighted means of the actual real s-th powers. The weighted mean preserves the source order `A^(1/2) * (A^(-1/2)*B*A^(-1/2))^t * A^(1/2)`. The right expression uses the actual aggregate sums and exactly the outer-middle-outer exponents `(1-t)*s*r*p/2`, `t*s*r*p`, `(1-t)*s*r*p/2`, followed by exponent 1/p. The declaration's argument order (s,t,r,p) and the conjecture's quantifier order (t,s,r,p) are passed consistently. The witness is s=t=1/2 and r=2, so sr=1 exactly; every p>0 remains quantified in the public counterexample. Choosing p=1 is sufficient for the full negation and would not narrow that logical result.

All matrices are over ℂ. The real rational witness is embedded in this same complex matrix algebra. `Matrix.PosDef` means the actual Hermitian positive-definite quadratic-form predicate, not an entrywise or real-only substitute. The generic n=0 case in the operator-norm admissibility export does not introduce vacuity into the original conjecture, whose dimensions are explicitly positive; the norm axioms are also valid on the zero-dimensional vector space.

## Genuine CFC and norm definitions

`spectralPower` explicitly invokes Mathlib `CFC.rpow`; the full elaborated definition selects the actual matrix partial order/star ring/CFC instances. `geometricMean` uses these real CFC powers, including both negative half powers. The witness's natural squares elaborate through `Matrix.semiring`, not the Pi pointwise-power instance. The future proof must identify its explicit rational candidates with these actual CFC expressions; those identities are required conclusions of `counterexample`, and no candidate root, Riccati theorem, symmetry/covariance law or spectral approximation is assumed in the statement.

`operatorNorm A` is `‖Matrix.toEuclideanCLM A‖`. I inspected the pinned Mathlib definition in `Analysis/CStarAlgebra/Matrix.lean`: `toEuclideanCLM` is the natural star-algebra equivalence from matrices to continuous complex-linear endomorphisms of `EuclideanSpace ℂ (Fin n)`, built from the standard orthonormal basis. The fully elaborated norm is `ContinuousLinearMap.hasOpNorm` on that space. It is therefore the genuine Euclidean operator norm, not the default entrywise norm.

The custom `IsUnitaryInvariantNorm` predicate contains exactly the ordinary complex norm axioms: nonnegativity, zero iff the matrix is zero, triangle inequality and absolute homogeneity for every complex scalar. It then requires invariance under two independent unitary factors U,V, each characterized by both inverse-adjoint identities. Both identities are redundant for finite square matrices but true for every unitary, so they do not restrict the original class. No operator-norm-specific property is added to the universally quantified norm predicate. The first required export proves that the concrete operator norm satisfies every one of these axioms in every dimension. This supplies a nonvacuous witness for the predicate and makes the later choice of norm a theorem, not an assumption.

## Independent exact numerical reconstruction

The independent script in `statement-referee-2-evidence/reconstruct.py` uses only Fraction arithmetic. It verifies C,E>0, S=Sᵀ with S²=I, C²+E²=I, all four actual input matrices' positive leading principal minors, and both aggregate sums exactly I. In particular, the determinants of the two diagonal inputs are 63504/1151329 and 490000/1151329; the conjugated inputs retain those strictly positive determinants and have strictly positive first diagonal entries.

I independently reconstructed D=SES, D₂=SCS, δ=5/3 and δ₂=3/5, checking δ²=det(D)/det(C) and its second-pair counterpart. The first scalar is h=61697295/8682716; the second is h₂=111055131/43413580. If T=D+δC and T₂=D₂+δ₂E, both are positive definite and both exact scaled Riccati identities hold:

`T C⁻¹ T = h D`, and `T₂ E⁻¹ T₂ = h₂ D₂`.

These checks provide an independent mathematical route for validating both positive geometric-mean candidates, not only the source's asserted symmetry/covariance shortcut. In the eventual Lean proof the positive-root/Riccati uniqueness bridge itself must still be proved using actual CFC, as the target requires. The numerical script is not a formal certificate or an assumed theorem.

The reconstructed squared first mean is

`G² = [[3516940,616000],[616000,6547660]]/12158163`,

and the squared second mean is

`H² = [[4699660,-1601600],[-1601600,5364940]]/12158163 = S G² S`.

Their sum is exactly the stated witnessL. Direct rational multiplication gives `L*(1,-4) = (1351000/1350907)*(1,-4)` and `1351000/1350907 - 1 = 93/1350907 > 0`. The vector is nonzero. The final Challenge requires this actual eigenvector identity, a lower bound on the genuine operator norm, and the actual right operator norm equal to one. It does not replace the matrix norm by the candidate eigenvalue. No complete singular spectrum is needed: an eigenvector and the norm inequality for the associated Euclidean linear operator suffice.

The actual CFC right matrix is required to equal I for every p>0, using the proved aggregate identities. Every matrix-function identification, norm bridge and strict inequality remains a consequence to prove. The scalar LeanCert point comparison therefore cannot be mistaken for a complete solution on its own.

## Nonvacuity, scope and attribution

I tried to produce a vacuous or narrower reading of the new predicates and found none. The full norm quantifier is preserved and its concrete norm witness must be proved. The rational candidate matrix's equality to the actual nonlinear left expression is a conclusion. Positive definiteness of all four inputs, the aggregate identities and the actual spectral/norm conclusions are all theorem conclusions. The ultimate export is the negation of the complete original universal assertion, with no manuscript theorem or unproved numerical lemma supplied as a hypothesis.

This is one coherent canonical target. It does not claim to refute narrower parameter regimes already established in the source literature. Mathematical authorship remains with Matthew J. Colbrook; George Stepaniants receives formalization credit with the Department of Computing and Mathematical Sciences, California Institute of Technology affiliation. No George email is present in the reviewed formalization files.

I applied the relevant Tau Ceti correctness/faithfulness, scope and attribution rubrics from the pinned local TauCetiReview checkout. For this repository, the explicitly requested canonical MI-21 target supplies the project scope; no unrelated Tau Ceti roadmap gate is imposed. Kernel trust and proof-quality auditing are reserved for the later final proof review. Only the standard axioms propext, Classical.choice and Quot.sound are permitted in completed exports.

## Independent elaboration evidence

The author's recorded statement build passed 2710 jobs with exactly three deliberate Challenge placeholder warnings. Independently, I compiled Definitions.lean into a fresh local module prefix, prepended that prefix to LEAN_PATH, then compiled Challenge.lean against that fresh definition artifact and inspected the resulting elaborated declarations. All three commands exited zero. Definitions emitted no warning; Challenge emitted exactly the expected three placeholder warnings. The full inspection confirms the actual CFC instance, natural matrix-ring powers, complex scalar homogeneity, genuine Euclidean operator norm and the full original quantifiers.

Raw logs and commands are retained in `reviews/statement-referee-2-evidence/`. The source manifest records reviewed source hashes. No mathematical source was edited by this referee. This approval opens only the statement gate when the other independent referee also approves; it does not substitute for implementation, final proof referees, axiom checks, or authoritative Linux Comparator.

Evidence SHA-256 values:

- `statement-referee-2-evidence/execution.json`: `59dd68010dc9e233d309ce068b29fa63125a1b68a61ba0ed99603ddc65b72e4e`.
- `statement-referee-2-evidence/definitions.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `statement-referee-2-evidence/challenge.log`: `1bde1aae4fdb2ff9975e2c10a48776b647a6a4a6e98b4009e6c18dd0122e1cb6`.
- `statement-referee-2-evidence/inspection.log`: `d2051288ec6ddefb599f3fa2e4e330e1423416fe3e7a5fe61b9ae4da844ab1b4`.
- `statement-referee-2-evidence/reconstruct.py`: `04a68dd338d7f59a135a9331be936494034615bcb995230f9db7762229af3dd8`.
- `statement-referee-2-evidence/numerical-reconstruction.json`: `3637af2c29027390181ba398845b7a51172a905b84927478c8bb421487adf6b9`.
- `statement-referee-2-evidence/review-source-manifest.json`: `1f9d6dff357952002094e181b80d00879d004bc757f2cf30ca566bcd57032040`.
