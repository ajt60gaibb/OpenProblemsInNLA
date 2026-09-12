# MI-06 independent final proof referee 2 — PASS

Date: 12 September 2026. Reviewer: OpenAI Codex agent `/root`, independent of implementer `/root/formal_review_standards`. **Approve the frozen complete mathematical proof for subsequent Linux verification. No mathematical correction is requested.** This is an independent AI-agent review, not external human peer review or an operational Linux verdict.

I read the complete original canonical target and Colbrook manuscript, every Definition, every Challenge and Solution signature, and the entire Proof implementation. I also inspected the actual pinned Mathlib CFC, positive-root, matrix-order, unitary, quadratic-form and finite-rank results used in the argument. The earlier two independent statement approvals preceded implementation; their files and all three frozen statement files remain unchanged. The source counterexample and its scope remain correctly attributed.

## Mathematical fidelity and substantive proof

The final declaration negates exactly the original assertion over all positive dimensions and all arbitrary complex matrix pairs, with two arbitrary complex unitaries allowed to depend on the inputs. The coefficient is the actual nonnegative `Real.sqrt 2`. The elaborated order is genuine PSD order of right minus left, and the arithmetic symmetric modulus is the average of genuine `CFC.abs X` and `CFC.abs X.conjTranspose`. No positivity, realness, invertibility, independence or commutation hypothesis narrows the original inputs. A rational three-dimensional witness suffices for its universal negation. The separate stronger informal theorem excluding every finite constant is not among these exports.

The first export proves the actual CFC positive-square-root identity for every complex matrix. The generic internal root helper uses `CFC.sqrt_unique` with both an actual square identity and a proved positive candidate; it does not assume a root table. For all six witness occurrences, exact matrix multiplication verifies the correct conjugate-transpose Gram product. Two positive roots are explicit positive multiples of outer products and the remaining occurrences are positive diagonal matrices. All three arithmetic averages and both rank-one decompositions then follow from the proved CFC equalities. I compared these computations to the independent exact rational reconstruction already performed at the unchanged statement boundary.

The nonzero orthogonal-vector lemma is fully generic over any two complex vectors in dimension three, including zero or dependent pairs. The implementation constructs a complex-linear map into dimension two using the two conjugate dot products. Assuming injectivity contradicts the actual finite-rank inequality 3≤2. A difference of distinct equal-image vectors gives a nonzero kernel vector. Its explicitly defined sum of complex norm squares is strictly positive. There is no sampled unitary, independence assumption, unit-vector normalization or hidden nonzero-vector hypothesis.

The generic quadratic-form lemmas use the real part of the genuine conjugate-vector form. PSD nonnegativity is obtained from `Matrix.PosSemidef.dotProduct_mulVec_nonneg` and the actual complex nonnegative order; monotonicity follows from the PSD difference. Thus real-part forms are a legitimate obstruction to the original matrix order, not a substituted definition of that order.

Unitary conjugation preserves the identity using the actual group property, maps uu* to (Uu)(Uu)*, and preserves PSD. On the common kernel vector, the two rank-one terms vanish. The two subtracted conjugated projectors have nonnegative forms, giving each upper bound of one eighth times squared length. A proved PSD diagonal remainder gives the lower bound of three eighths for the actual sum modulus. The public bounds theorem derives all three bounds for every complex unitary pair from these analytic lemmas and the actual CFC identities; it does not take any of them as assumptions.

The scalar chain is correct and substantive. The sole LeanCert call proves 2<9/4 in explicit kernel mode. `Real.sqrt_lt_sqrt` consumes it to prove sqrt(2)<3/2, followed by division by positive four. For the common positive-length vector, the assumed domination would force

(3/8)·squaredLength(w) ≤ (sqrt(2)/4)·squaredLength(w),

contradicting the strict scalar bound after multiplication by that positive length. Instantiation of the full conjecture at the explicit dimension-three pair then proves its unconditional negation. No spectral approximations, interval subdivision, numerical matrix roots or unitary searches enter this proof.

## Independent fresh checks and retained certificate

I compiled Definitions, Proof and Solution sequentially into a fresh root-referee artifact prefix. All three commands exited zero, with no warnings or errors. All 46 internal Proof declarations and all six public declarations passed their kernel trust assertions; the 52 fresh axiom reports are each exactly `{propext, Classical.choice, Quot.sound}`. Every mathematical/configuration file was unchanged before and after these checks. The six public signatures also agree with Challenge after whitespace normalization, and Comparator declares no replaceable definition names.

My separate read-only inspection starts at the public conjecture negation and walks its actual project proof dependencies. It inspected 90 reachable project declarations, including generated auxiliaries. It found the scalar certificate in that dependency graph and required its actual body to retain `LeanCert.Validity.verify_strict_upper_bound_dyadic_checked`. The printed certificate is the explicit singleton [0,0] calculation. This checks actual proof-term consumption rather than merely the presence of a LeanCert import or unused scalar lemma. The same fresh inspection prints the fully elaborated conjecture, modulus, length and quadratic-form definitions and all six public types.

All ten actual dependency Git HEADs match the locked manifest and have clean tracked source. The project pins Lean v4.33.1, LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. These checks ran on macOS arm64 and reused the matching dependency artifacts. They are not a fresh dependency source build, Linux Comparator execution or sandbox/kernel-export replay. The six deliberate Challenge placeholders remain confined to its separate template and are absent from Solution's import graph.

Fresh execution receipts, all raw outputs, exact source identities, library hashes, signature checks and reproducible inspection scripts are retained in [proof-referee-2-root-evidence](proof-referee-2-root-evidence/). The inspection log SHA256 is `91c656d5dc244df37fc500c268817c7fd5af05e7ba26cc7cf5fcbd7005f241ae`. The source scan is supplementary to the actual transitive axiom checks.

## Review scope and remaining publication gates

I applied the relevant Tau Ceti correctness/faithfulness, scope, computation, reuse and attribution rubrics at `afb424eda89e8ac96d9eb69f6a88972055a4cd1b`, adapted to the complete permanent MI-06 target. Existing Mathlib CFC and finite-dimensional APIs are reused without changing dependency sources. The homogeneous kernel-vector argument substantially reduces computation without weakening any original quantifier.

Mathematical counterexample credit remains Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Formalization credit is George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI assistance and without George's email. No official Tau Ceti or external human approval is asserted.

Referee 1's independent final approval, truthful manifest metadata and actual Linux Comparator/default-kernel replay remain separate gates. No canonical promotion, commit or publication was performed by this review. A substantive mathematical change reopens the affected final reviews.

| Frozen file | SHA256 |
| --- | --- |
| `NLA/MI06/Definitions.lean` | `a89c6604d36aec8ae3428df7663a2dbb6f2f923b13ca5f7746aaf4f424cb29d2` |
| `Challenge.lean` | `7774d76c9e362c0f808ee4c1fec3b5607359048d5af82d0e99f60b74c52326dc` |
| `NUMERICAL_TARGETS.md` | `792aa98aa94d18d7b49e4e4b66edca89881f1e38cf51c3aacfed8525644509a4` |
| `NLA/MI06/Proof.lean` | `3c1fdf9ba68e850d26d1307ce6ac2a1e9a1037aba5645bda10aa68e7c3d44145` |
| `Solution.lean` | `389fac775519a84b79b68811e141df5f466e9818469efca889c550e3110b806a` |
