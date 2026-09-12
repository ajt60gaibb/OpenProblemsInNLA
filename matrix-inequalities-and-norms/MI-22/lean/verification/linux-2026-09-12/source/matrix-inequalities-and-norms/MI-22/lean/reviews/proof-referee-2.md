# MI-22 independent final proof referee 2 — APPROVE

Reviewer: OpenAI Codex agent `/root`, 12 September 2026, independent of implementation author `/root/leancert_examples`. I previously independently approved the frozen statements before implementation. This final review covers the complete current proof, every advertised export and the source correspondence. It approves local proof completion; actual Linux Comparator, operational audit and publication remain later gates.

## Reviewed immutable boundary

The complete local proof freeze `verification/proof-freeze.json`, SHA256 `f1c267a6aa600074d3b054863926d5f9cdbf6b0eadb83912a912277ac54018a0`, binds 104 project files and eight original sources. I verified every hash and the original Git blobs at `8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`. The two prior statement approvals and all mathematical definitions, eight Challenge signatures, exact numerical targets, source correspondence, Comparator configuration and dependency pins are unchanged.

The only authorized statement-package difference is the build registration: the exact original lakefile is archived with SHA256 `69b0f047c2c8753489c89814023bcc846c751fc869ce3f9233ab50097308db9b`, and appending only the Solution library produces current SHA256 `750d9ab9828e30c33cee900858a13da3aa6906cd87f84cb757851866db62f5dd`. I checked that exact append and the recorded prior authorization. `defaultTargets = ["Challenge"]` remains unchanged; use **`lake build Solution`** for the complete proof. No mathematical statement was weakened to make a proof pass.

Reviewed proof SHA256: `9d5140c36dd23c4d726e1f2855cfe4ade18999f868c2df7e7f784eab2bc08c9c`. Public Solution SHA256: `6b37f8df6544f93df123dc746db24c3b3ccd4c6a3e318732ef09946d639e556c`.

## Complete target and actual semantics

The compiled `WeightedLogMajorizationConjecture` still quantifies every positive dimension, all complex positive-definite A and B, and every real t in [0,1]. `SingularLogMajorized` retains each nonempty proper prefix and equality of complete products. The noncommuting order is exactly `A^t (A #_t B) B^(1-t)`. A genuine dimension-three first-prefix counterexample is sufficient to negate the full universal statement; the proof need not falsify each separate conjunct.

I read every source line in Definitions, FunctionalCalculus, Norms, SingularValues, Witness, ExactData, Proof and Solution, and inspected the actual compiled predicates again. `spectralPower` is actual `CFC.rpow`, `operatorNorm` is the norm of `Matrix.toEuclideanCLM`, and `singularValue` is Mathlib's singular-value family of the actual Euclidean linear map. These are not substituted lists, entrywise powers, or assumed numerical proxies.

The generic CFC spectral theorem proves equality with the genuine Hermitian unitary diagonalization for every real exponent of a positive-definite matrix. The singular-value implementation proves nonnegativity, decreasing order, zero extension, and the actual repeated adjoint-Gram eigenvalue square roots. It proves the first singular value equals the genuine operator norm from sorted Hermitian eigenvalues, the actual adjoint/matrix conversion and the C-star Gram norm identity. I checked the relevant pinned Mathlib definitions and proofs, including the finite singular-value APIs, CFC composition and self-adjoint power-norm theorem. Both full positive dimensions and multiplicities remain intact.

## Exact counterexample and complete contradiction

The witness is explicitly disclosed as an exact rational adaptation of Matthew J. Colbrook's method, preserving his diagonal A but using `B=D T^8 D`, not his printed B. That divergence changes neither the original target nor the attribution of the source method. My earlier independent Fraction reconstruction remains in the unchanged statement-review evidence.

Exact LDL and nonzero determinant prove T positive definite; diagonal positivity and congruence prove A and B positive definite. Real-power composition proves every required principal-root identity. In particular the actual `Y=B^(1/8)` satisfies Y^8=B, B^(7/8)Y=B, and the actual original left product L satisfies L Y=N, with the noncommuting order preserved. These are conclusions, not hypotheses.

All rational tables are kernel-proved finite matrix equalities. Three non-diagonal squarings give T^2,T^4,T^8. Additional exact calculations verify B, AB, the needed N row, the unit vector, trace bound and full squared Frobenius bound. The generator is a convenience for producing proposed rational data; it is not an oracle or premise in Lean.

The genuine self-adjoint power norm gives ||Y||^8=||B||≤Re tr(B)<4^8, hence ||Y||<4. The exact tested coordinate exceeds 44000 on a unit Euclidean vector, so 44000<||L|| ||Y||≤4||L||, implying 11000<||L||. The genuine Frobenius bound gives ||AB||<10500. Actual singular-value/norm equality turns this into the first-prefix violation, and the final theorem applies the original universal hypothesis at n=3,t=1/8 and contradicts that violation.

## LeanCert, trust and independent execution

The retained LeanCert calculation is exactly the strict point inequality **10500<11000** on the singleton [0,0]. It does not certify fractional matrix powers or replace the other exact algebra. I inspected its actual term: `LeanCert.Validity.verify_strict_upper_bound_dyadic_checked` receives a Boolean proof `of_decide_eq_true (id (Eq.refl true))`. The actual compiled counterexample includes `LT.lt.trans NLA.MI22.numerical_separation`, and the full negation consumes that counterexample. Thus its use is retained and material to the exhibited proof chain. No interval subdivision or numerical eigenvalue search is needed.

I ran eight source elaborations into a new unique temporary object prefix, building Definitions, the six implementation modules and Solution sequentially. The old project `.lake/build/lib/lean` path was explicitly removed from LEAN_PATH. All eight commands passed, without warnings or errors; all 17 kernel assertions and transitive axiom reports contain exactly `propext`, `Classical.choice`, and `Quot.sound`. This local macOS run reuses ten clean dependency caches at their exact pins and does not claim Linux isolation or a full dependency-source rebuild.

A ninth, independent compiled-environment inspection passed. It traversed **195** project declarations and checked **21** selected actual mathematical dependencies, including the original singular-value and Gram APIs, true CFC composition, self-adjoint norm power, exact witness identities and the LeanCert validity theorem. The full dependency graph, printed actual predicates and relevant retained proof terms are in `proof-referee-2-root-evidence/inspection.log`, SHA256 `2e4ae313ca0178f7b61f0a82012b8b49dfb315dfac5ff5a3c1fac9e287fb79b5`. Source signatures match all eight frozen Challenge statements exactly; this local check does not replace the later Linux Comparator.

The independent audit scanned all eight implementation source files: no `sorry`, `admit`, custom axiom, unsafe implementation, native decision, compiler-trust shortcut, environment mutation or import of Challenge occurs. The eight intentional Challenge placeholders remain isolated statement targets. The Comparator definition-exception list is empty and the whitelist is precisely the standard three. Every frozen input and original source remained unchanged during review. Audit SHA256 `84a6ffd932270adce8bd175efcb6f9d228b65956c9ff16044070b465f1807ae4`; execution SHA256 `a3b0272cca788b26c1e994520b4034d1a747bbf8dbb918904228922037a41ba7`; clean dependency audit SHA256 `3f52d945a028fd87536ed26f978f1603c52994ab1c0d40f22fb768dc1de5b6eb`.

## Verdict and remaining gates

**APPROVE all eight exports and the full canonical negative resolution.** The review applies the pinned Tau Ceti correctness, nonvacuity, domain fidelity, definition integrity, axiom, trust, witness-semantics and reproducibility standards within NLA scope. No mathematical correction was required. No stronger conjecture premise, finite-only replacement of the original target, unproved spectral bridge or decorative certificate was found.

Preserve all original source attribution. Formalization credit belongs to George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance; no contact email is added. My review is independent agent review, not external human peer review or source-author endorsement. Canonical status, commits and publication were not changed by this final proof review. Truthful candidate metadata, actual Linux verification and its independent operational audit are still required.
