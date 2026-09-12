# MI-07 independent final proof referee 1

**Verdict: PASS for all seven exports at the hashes below.** The proof gives a complete negative answer to the original constant-one triangle conjecture, using the actual CFC matrix modulus and proved root-sequence limits. No mathematical correction is requested. Linux Comparator, the other final referee, and publication metadata are separate gates; this review alone does not promote the canonical status.

Reviewer: OpenAI Codex AI agent `/root/solved_statement_inventory`, 12 September 2026. I independently reviewed the statements before implementation and did not author or modify this mathematical proof. The proof implementer is agent `/root/leancert_examples`. This is independent agent review, not external human peer review or an official Tau Ceti service verdict.

## Sources, target, and scope

I read the entire canonical README, Colbrook standalone TeX and submission note, the frozen Definitions, Challenge and numerical targets, all of FunctionalCalculus and Proof, Solution, and the implementation completion record. The three informal files remain byte-identical to upstream `e7252e5307781a7c897bca6cb124f6ab838f6809`. All 18 files bound by the implementer's freeze, including the prior statement approvals, retained their hashes. The [input record](../verification/referee-1/inputs.sha256.json) binds these exact sources.

The target still quantifies every positive dimension and every pair of complex square matrices, with existentially chosen arbitrary complex unitary matrices. Its comparison is ordinary PSD order. There is no positivity, self-adjointness, commutation, reality or rank restriction on the arbitrary inputs. The final export negates that entire predicate. The explicit rank-one witness is one admissible complex instance, and the contradiction excludes every complex unitary pair, so the complete original yes/no question is settled.

The source proves a stronger statement excluding every finite domination constant. This formalization proves the original constant-one assertion false, using the source family at `t=5/12` and a trace obstruction. It does **not** formalize the stronger varying-parameter theorem or claim generic convergence for all complex matrices. This scope matches the canonical original target and both frozen statement approvals.

## Actual CFC and limit mathematics

`matrixModulus` is the genuine `CFC.abs`, whose definition is the CFC positive square root of `XᴴX`. The generic exported square-root and positivity theorem uses that actual definition and `CFC.abs_nonneg`. Each concrete modulus is identified by `CFC.sqrt_unique` after proving its candidate is PSD and its square equals the actual ordered Gram matrix. Those equations are conclusions of exact matrix algebra, never assumptions.

The two projections are Hermitian and idempotent by exact matrix multiplication. Their PSD properties follow from the true Gram-matrix theorem. The complement of the first projection is a nonnegative diagonal matrix. `spanningSum` is PSD as a sum, and its exact nonzero determinant proves positive definiteness using Mathlib's matrix positivity criterion. My independent `Fraction` reconstruction rechecks all six Gram-square identities, their candidate PSD minors, and `det(spanningSum)=25/169`; the [script and result](../verification/referee-1/numerical_check.json) are supplementary evidence, not Lean premises.

The proof's handling of singular matrices is essential and correct. `rpow_projection` restricts the actual real spectrum of a PSD idempotent to `{0,1}`. At every strictly positive exponent, zero maps to zero and one maps to one. It therefore retains the projection's nullspace. The proof never substitutes the unital exponent-zero value at the singular projection.

`rpow_real_smul` derives positive-scalar compatibility from the real CFC composition and scalar-map APIs, with the necessary nonnegative-scalar and positive-exponent hypotheses. `posDef_rpow_tendsto_one` applies continuity in the exponent only to a positive definite matrix: Mathlib's actual eigenvalues are strictly positive, its genuine Hermitian CFC formula conjugates their diagonal powers by its actual eigenvector unitary, and finite entrywise continuity gives convergence to the identity. No spectrum or convergence fact has been assumed. I inspected the relevant pinned projection-spectrum, Hermitian CFC and positive-eigenvalue APIs.

The complete root sequences, at every index `r`, are proved to be:

- `2^(1/(r+1)) P` for the singular projection witness, tending to `P`;
- `(5/12) I` for the nilpotent witness, identically at every index;
- `(13/12) R^(1/(r+1))` for their sum, tending to `(13/12) I` because `R` is positive definite.

The reciprocal exponents are proved positive and tend to zero; the inner natural exponents are the actual matrix-ring powers. The inspected elaboration confirms the outer operations are matrix `CFC.rpow`, not pointwise function powers. The generic spectral-norm export uses the genuine L2 operator-norm instance and the usual norm-convergence theorem, so the topology is the required finite-dimensional matrix topology and also operator-norm convergence.

Every use of `maximalModulus` in the witness is identified by applying the proved `limUnder_eq` bridge to one of those actual convergences. The totalized limit's fallback value is never used. No convergence premise is added to the public counterexample or final negation.

## Every-unitary contradiction and LeanCert

For arbitrary genuine unitary `U,V`, trace cyclicity and `UᴴU=I` prove that conjugation preserves trace. The actual maximal-modulus identities yield left trace `13/6`, every right-orbit-sum trace `11/6`, and right-minus-left trace `-1/3`. If the claimed PSD domination held, Mathlib's `Matrix.le_iff` would make that difference PSD, hence its trace nonnegative. The real part of the exact negative trace contradicts this. There is no unitary search or restriction to orthogonal, diagonal, or chosen unitary representatives.

The only LeanCert call proves `0 < 1/3` with explicit `trust := kernel`. My independent [certificate inspection](../verification/referee-1/certificate-inspection.log), using freshly compiled proof artifacts, prints the actual `LeanCert.Validity.verify_strict_upper_bound_dyadic_checked` certificate: constant zero on the point interval `[0,0]`, rational bound `1/3`, precision `-53`. It visibly remains in `scalar_gap_positive`, is consumed by `no_unitary_domination`, and reaches the full conjecture negation. It is substantive certification, not an unused demonstration. I inspected the pinned verification router: explicit kernel mode cannot fall back to native verification, and `#assert_trust kernel` rejects native-compiler, sorry and custom axioms.

This approach minimizes computation appropriately: six exact order-two polar checks, two projection identities, one determinant, and one scalar point certificate suffice. There is no interval subdivision, approximate eigenvalue calculation, numerical matrix square root or search over unitary matrices.

## Independent execution and trust

I independently re-elaborated Definitions, FunctionalCalculus, Proof and Solution into a newly created separate prefix, placing those fresh artifacts first in `LEAN_PATH` for each dependent module. All four actual commands exited zero, with no warnings, taking approximately 8, 12, 33 and 9 seconds respectively. I then independently elaborated the unchanged Challenge and reran the full elaboration and certificate inspections against those fresh artifacts. All three further commands exited zero; only the seven intended Challenge placeholder warnings occurred. The [command record](../verification/referee-1/checks.json) and raw logs retain source and output hashes. Existing compiled dependency artifacts were reused. This is local macOS arm64 execution, not authoritative Linux Comparator or a fresh Linux dependency rebuild.

All 16 internal and seven public kernel-trust assertions passed during these independent commands. Every one of the 23 corresponding transitive axiom reports contains exactly `propext`, `Classical.choice`, and `Quot.sound`; see the [independent axiom audit](../verification/referee-1/axiom-audit.json). The proof dependency chain contains no holes, custom axioms, native tactics, unsafe declarations or Challenge import. The scoped elaboration-transparency settings in two helpers change proof elaboration, not the mathematical definitions or kernel trust.

Every one of ten checked-out package HEADs matches its pinned manifest revision, without tracked source changes. Lean is `4.33.1`, LeanCert is `621a43d7cf21f87872392a01e874f2f1dbddc926`, and Mathlib is `0df444a360eaa60ab8c11dca51a86af692955474`; [dependency and interface hashes](../verification/referee-1/dependencies.json) bind this inspection. All seven public signatures match the frozen Challenge literally after whitespace normalization. The [source identity check](../verification/referee-1/statement-identity.json) supports, but does not replace, real Linux Comparator identity and default-kernel replay.

## Scoped Tau Ceti assessment and attribution

The relevant [Tau Ceti rubrics](https://github.com/TauCetiProject/TauCetiReview/tree/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/rubrics) were applied to correctness, fidelity, scope, proof quality, generality, reuse, API, documentation, and attribution within this repository's MI-07 task. The proof completes one canonical target with its genuine analytic prerequisites. Reuse searches found and the proof uses actual Mathlib CFC composition, spectral representation, positivity, norm-topology, trace, and unitary APIs. The small new CFC helpers have concrete consumers. Public wrapper declarations preserve the independently frozen Comparator boundary; they do not introduce a competing mathematical target.

The analytic singular/positive-definite distinction and the computational plan are documented, and the helper decomposition makes the proof auditable. No blocking proof-quality or semantic finding remains. Initial statement-stage notes are retained as historical records; final metadata must accurately describe the completed proof and remaining remote-verification gate.

Mathematical authorship remains **Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Formalization authorship is **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. No George email or human/source-author endorsement is added. I made no mathematical source, canonical status, commit or push changes.

## Bound mathematical files

| File | SHA-256 |
| --- | --- |
| `NLA/MI07/Definitions.lean` | `369e99eaf3df8a8bbfb214973129ab71fbc95445ba9d176e91d52bca3bc46bc5` |
| `Challenge.lean` | `62fee2804dc12a4ad7edecfa8c1dda2dc39acc2d94475d29805e8e55c3288a59` |
| `NUMERICAL_TARGETS.md` | `70272f54de929a95347db186b09b66d534313eed87ab7daa8e7fe5c8aaa8bd1e` |
| `NLA/MI07/FunctionalCalculus.lean` | `0963940bbed1818e7b8240129de01e832660f045dbfcabf578fb11d99949553a` |
| `NLA/MI07/Proof.lean` | `55f400e703994c3967a245495f6ad1ebc1999133cfd748185c81ef263178d8a3` |
| `Solution.lean` | `e460594ac018c8a1e966d88012b07c4ada8743957a414cbdfff8b790d54c07ee` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lakefile.toml` | `eb8266ae962777bdd0ec8208bb4611c1876bdcbb879602a41ff972c2b58a19ab` |
| `lake-manifest.json` | `068377fdaf5079cfc3aea6cf0e8fc35a91ccd3da5b20670802a4df1d070bd073` |

The [evidence manifest](../verification/referee-1/evidence-manifest.json) binds the independent command, algebra, dependency, axiom, signature and certificate records. Mathematical changes reopen affected review gates.
