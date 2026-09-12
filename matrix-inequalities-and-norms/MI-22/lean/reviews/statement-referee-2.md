# MI-22 independent statement referee 2 — APPROVE

Date: 12 September 2026. Reviewer: OpenAI Codex agent `/root`, independent of statement author `/root/leancert_examples`. **The frozen definitions, eight Challenge signatures and numerical specification are approved for implementation.** No statement correction is required. This is independent AI-agent statement review, not a completed proof, human peer review or Linux verification. I reached these conclusions independently of referee 1's written report.

I read the complete canonical question, Colbrook's source argument, all definitions and Challenge declarations, and the numerical plan and source correspondence. Fresh separate-prefix elaboration of Definitions, Challenge and an actual-environment inspection passed. All 27 frozen project inputs and eight original source files match their hashes and the immutable source revision `8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`. No Proof or Solution implementation exists at approval.

## Complete target and actual semantics

The universal conjecture retains every positive dimension, arbitrary complex positive definite A and B, and every real t in the closed interval [0,1]. Its left side is exactly A^t (A #_t B) B^(1−t), with both A^(−1/2) factors and the original noncommuting order in the weighted mean. There is no commuting, rational-entry or witness-specific premise in this full target.

`SingularLogMajorized` requires every nonempty proper prefix-product inequality and equality of the product of all n singular values. Zero-based indices 0 through k−1 represent the original first k entries. The n=1 equality is retained. The counterexample may fail just k=1 at n=3, but the negated proposition remains the complete original relation, including its full-product requirement.

The singular values are Mathlib's actual `LinearMap.singularValues` of `Matrix.toEuclideanLin A` on complex Euclidean space. I inspected the library definition and its finite-dimensional eigenvalue, monotonicity and zero-tail APIs. It is the decreasing square-root list of actual adjoint-composition eigenvalues, with multiplicities and zero extension, not a supplied list or arbitrary spectral proxy. The first export explicitly proves all these properties and equality of entry zero with the actual operator norm. Positive dimension excludes the empty-space endpoint in that bridge.

Real powers use genuine `CFC.rpow` with matrix order. The second export proves its principal spectral decomposition for every positive definite complex matrix and every real exponent; it is not limited to the rational witness. Matrix functional calculus, Hermitian eigenvalues and the actual unitary eigenvector matrix supply the claimed principal-power meaning. These identifications remain proof obligations, not hypotheses.

The operator norm is explicitly that of `Matrix.toEuclideanCLM` on complex Euclidean space. The actual elaborated environment uses `ContinuousLinearMap.hasOpNorm` and the L2 space. Frobenius squared sums `Complex.normSq` of all entries. The generic third export proves both the complete Frobenius upper bound and the action-coordinate lower-bound mechanism for arbitrary matrices and vectors. No default entrywise matrix norm or one-coordinate norm replaces these objects.

## Exact rational adaptation and numerical reduction

The adapted witness is clearly distinguished from the manuscript's printed integer B. It keeps A=diag(256,1/256,1), but defines D=diag(16,1/16,1), T equal to the stated symmetric integer matrix divided by 8192, and B=DT⁸D. The original B and approximate-root residual argument are not advertised as formalized. This is a legitimate new rational witness for the same complete target, with original counterexample and method credit preserved.

I independently reconstructed every rational matrix using Python `Fraction` and eight successive multiplications, without importing the author's checker or power table. The entries of T are uniquely nearest dyadic values to the source's R at denominator 8192. Exact multiplication confirms the specified unit lower-triangular LDL factorization and the positive pivots; the integer leading minors are 4616, 254196983 and 1555181999141. I checked D and Dinv, the actual adapted B and its symmetry, Dinv B Dinv=T⁸, and that this B differs from the source's integer B.

The proposed A^(1/8)=F=diag(2,1/2,1) and A^(5/8)=E=diag(32,1/32,1) satisfy F⁸=A, E⁸=A⁵ and FD=E exactly. Positivity and genuine CFC identities still must be proved in Lean; these rational identities alone do not establish them. The vector v=(0,4/5,−3/5) has exact Euclidean norm squared one. Direct computation of N=ETDB and AB verifies all three strict rational tests:

- Re tr(B) is approximately 20497.89315, strictly below 4⁸=65536.
- Re (Nv)_0 is approximately 45616.01572, strictly above 44000.
- The squared Frobenius norm of AB is approximately 105373743.68504, strictly below 10500²=110250000.

The reconstruction record retains the exact fractions, complete matrices and strict margins. These decimals are only readable summaries, and no floating-point result is used to certify a sign.

The principal-power export retains every necessary analytic bridge as a conclusion. With Y equal to the actual B^(1/8), it proves Y positive definite, Y⁸=B and B^(7/8)Y=B. It also proves the actual weighted mean DTD and the correctly ordered identity L Y=N, where L is the original left product at t=1/8. These identities use functional calculus for powers of the same positive matrix and associativity; no commutation between A and B is presumed.

The planned bound on Y is sound: for positive definite Y, its genuine operator norm satisfies ||Y||⁸=||Y⁸||=||B||, and positivity gives ||B||≤Re tr(B)<4⁸. Thus ||Y||<4. Combining the exact unit-vector test with ||N||≤||L||||Y|| proves 11000<||L||. The independent Frobenius estimate proves ||AB||<10500. The exact first-singular-value identity then gives a strict reversal at k=1 and negates full log-majorization at the admissible t=1/8.

This removes approximate matrix roots, eigenvalue computations and interval subdivision. The numerical plan retains a single explicit kernel-mode LeanCert point certificate for 10500<11000, which must actually be consumed in the singular-value contradiction. All exact matrix arithmetic, positivity, CFC identities and norm bridges must still be proved. A disconnected certificate or assumptions supplying those bridges would not satisfy this approval.

## Independent checks and review scope

My fresh check removes the project's old artifact path entirely, compiles Definitions and Challenge into a separate prefix, and then inspects the actual definitions. All three commands passed; the only placeholders are the eight deliberate Challenge holes. My inspection makes 22 kernel-trust and transitive axiom checks on the definitions and witness objects; each uses at most `propext`, `Classical.choice` and `Quot.sound`. The author's separate 23-definition check additionally includes the Mat abbreviation. All ten locked dependency Git revisions are clean and match the manifest.

The Comparator selects exactly the eight reviewed exports, has empty `definition_names`, and permits only the standard three axioms. Local checks are macOS elaboration using pinned dependency artifacts, not Linux Comparator execution or a full source rebuild of Mathlib. The numerical reconstruction is supplementary statement checking, not a proof of the universal theorem.

The complete inspection log has SHA256 `20c47f332a4c36729772d5469dcc646c77945246b2eeafce09e168bd4b5ca68f`; the independent reconstruction has SHA256 `90c7a2a16f9443e4c1316f5012282455c92bfe21fd13a59a26bba7c208bc464f`. Eleven evidence files are bound by [statement-referee-2-root-evidence/evidence-manifest.json](statement-referee-2-root-evidence/evidence-manifest.json), SHA256 `96e65c95d37df664b1038bd37433a09ff18ccd1302f255da8ed6f67685cd3d7a`. They include the actual instance inspection, fresh commands, immutable input audit, relevant library hashes, and independently written reconstruction source.

I applied the appropriate Tau Ceti faithfulness, correctness, computation, scope and attribution rubrics pinned at `afb424eda89e8ac96d9eb69f6a88972055a4cd1b`. This is not official Tau Ceti endorsement. The pinned Schiffer/Forsythe organization and existing exact CFC/norm techniques are appropriate references with attribution; no mathematical result may be imported as an unproved axiom.

Credit remains Matthew J. Colbrook for the original counterexample and method. Formalization and the disclosed rational adaptation are credited to George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI assistance and no email address.

Implementation may begin once both bound statement approvals exist. A substantive statement change reopens the affected review. Two independent final proof reviews, truthful `formalization.yaml`, actual Linux Comparator matching, default-kernel replay and standard-three-only trust remain mandatory before publication or canonical promotion. This review made no canonical edit, commit, push or PR.

| Frozen input | SHA256 |
| --- | --- |
| Definitions | `3a9398c2da3be1c71fd59de483042153cae1af55226f4b61ca9d7bd977ffd8f8` |
| Challenge | `503cc7280458d3a1dcc4c3a03b91bcb3ae7e7940961dcd12d86736a133923179` |
| Numerical targets | `3798f0d25414815e683cabfc77ab776a2a22e4929c1fab0ea4f49fbde8187c66` |
| Statement freeze | `d83d2a2baa1788f6e5ec284c70bb12d7618f4963a9426777a37b2af4135ed756` |
