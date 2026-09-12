# MI-22 independent final proof review — referee 1

**APPROVE / PASS for the complete frozen local formalization.** No mathematical correction is required. This does not assert successful Linux Comparator/default-kernel verification or authorize status promotion by itself.

Reviewer: OpenAI Codex agent `/root/solved_statement_inventory`, 12 September 2026. Implementation author: separate agent `/root/leancert_examples`. I reviewed the actual source and proof terms independently before reading the other final referee's conclusions. I had independently reviewed the statements, but did not implement or edit the mathematical proof.

## Exact reviewed boundary

The complete proof freeze `verification/proof-freeze.json` has SHA256 `f1c267a6aa600074d3b054863926d5f9cdbf6b0eadb83912a912277ac54018a0`. I verified all **104 frozen project files and eight original source files**, before and after my fresh checks. Each original source equals its Git blob at `8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`. I read the full canonical statement, full original/exported Colbrook proof and informal review, numerical targets, source correspondence, Definitions, Challenge, all six implementation modules and Solution.

| Input | SHA256 |
| --- | --- |
| Definitions | `3a9398c2da3be1c71fd59de483042153cae1af55226f4b61ca9d7bd977ffd8f8` |
| Challenge | `503cc7280458d3a1dcc4c3a03b91bcb3ae7e7940961dcd12d86736a133923179` |
| Numerical targets | `3798f0d25414815e683cabfc77ab776a2a22e4929c1fab0ea4f49fbde8187c66` |
| Source correspondence | `e501e9b1476986cf0764067bd5672b0dbdb4261a9daf99ddcb5c7f13b548c95b` |
| Proof | `9d5140c36dd23c4d726e1f2855cfe4ade18999f868c2df7e7f784eab2bc08c9c` |
| Solution | `6b37f8df6544f93df123dc746db24c3b3ccd4c6a3e318732ef09946d639e556c` |

The full exact helper/pin/source hashes are retained in `proof-referee-1-evidence/inputs-before.json` and `original-sources.json`. The original statement freeze is `d83d2a2baa1788f6e5ec284c70bb12d7618f4963a9426777a37b2af4135ed756`; both bound statement approvals precede the recorded implementation gate.

**One authorized build-only change:** the archived `verification/lakefile.statement.toml` equals the original lakefile hash `69b0f047c2c8753489c89814023bcc846c751fc869ce3f9233ab50097308db9b`. Appending exactly the recorded `Solution` lean_lib stanza produces current hash `750d9ab9828e30c33cee900858a13da3aa6906cd87f84cb757851866db62f5dd`. All other 26 original statement inputs are unchanged. No default target, dependency, definition, signature or mathematical assumption changed. The complete build command is **`lake build Solution`**; plain `lake build` still defaults to Challenge. `statement-integrity.json` records the exact comparison and authorization record.

## Fidelity and complete mathematical path

1. **Full target.** The canonical quantifier ranges are preserved: every positive dimension, every complex Hermitian positive-definite pair, and every real t in the closed interval [0,1]. `SingularLogMajorized` retains every proper nonempty prefix and equality at the full dimension. It is neither weak log-majorization nor a largest-value-only replacement. All eight Solution headers match the frozen Challenge headers exactly; the local header check supplements fresh elaboration and does not replace Comparator.

2. **Actual spectral objects.** `spectralPower` is genuine `CFC.rpow`. The generic spectral representation is proved for every positive-definite complex matrix and every real exponent using the actual Hermitian unitary diagonalization. Natural-power composition supplies the true principal roots. The singular-value family is Mathlib's descending, multiplicity-bearing square-root spectrum of the actual Euclidean adjoint composition, with zero extension. The first singular value equals the real operator norm by the positive Gram matrix, sorted Hermitian eigenfamily, adjoint/matrix-map identity and C-star norm identity. These facts are proved, not hypotheses or user-supplied lists.

3. **Norms and positivity.** The frozen norm is explicitly the norm of the Euclidean continuous linear map. `operatorNorm_eq_l2` identifies the exact scoped L2 instance. The generic Frobenius bound follows from positive Gram trace, and the actual coordinate/action bound uses a genuine Euclidean vector. Generic norm statements also cover dimension zero where their signatures permit it. Exact LDL equality, positive pivots and an invertible triangular factor prove T positive definite; ordinary positive powers and congruence prove A and B positive definite. No numerical eigensolver or assumed positivity certificate enters the proof.

4. **Disclosed adaptation and exact data.** The adapted B is exactly `D T^8 D`, and is explicitly different from Colbrook's printed integer B. My separate Fraction implementation parses the source R, confirms the unique nearest dyadic T, recomputes all powers by naive sequential products, and checks LDL, positive minors, diagonal/inverse identities, the unit vector and every strict rational margin. Independently parsing the actual Lean tables also reproduces all **48 entries** across T², T⁴, T⁸, B, AB and the required N row. Every table equality is additionally proved in Lean by exact finite algebra. The generator is not trusted.

5. **True roots through the final contradiction.** All A powers and the normalized root are proved by CFC. The other root Y remains the actual `B^(1/8)`, with proved positivity and `Y^8=B`. The noncommuting order is respected in `L Y=N`: only powers of the same B are combined, and T is never commuted through D. The C-star eighth-power norm and positive trace bound give `‖Y‖₂<4`. The true coordinate estimate `44000<Re(Nv)₀`, with `‖v‖₂=1`, forces `11000<‖L‖₂`; the exact Frobenius bound gives `‖AB‖₂<10500`. The strict first-singular-value reversal contradicts the mandatory k=1 prefix at n=3,t=1/8, hence the full original universal statement. Equality at n remains in its definition and need not be separately refuted.

## Fresh checks and retained trust

My `fresh_review.py` completed ten separate-prefix commands: Definitions, FunctionalCalculus, Norms, SingularValues, Witness, ExactData, Proof, Solution, Challenge, and my independent environment inspector. All exited zero. No old project objects were on LEAN_PATH; ten clean dependency checkouts matched their exact pins and their compiled caches were reused. This is local macOS Lean 4.33.1 validation, not a rebuild of Mathlib or execution of Linux Comparator. The only warnings were the eight deliberate Challenge placeholders; Solution imports no Challenge.

All 17 distinct internal/public audited declarations use exactly `propext`, `Classical.choice`, and `Quot.sound`. My inspector repeated the eight public trust/axiom checks, traversed **195 actual project declarations**, and checked 21 participating semantic dependencies. The actual final proof has direct edges from the full negation through the counterexample to `numerical_separation`, which calls `LeanCert.Validity.verify_strict_upper_bound_dyadic_checked`. A separate eleventh fresh inspection printed its auxiliary Boolean proof, `of_decide_eq_true (id (Eq.refl true))`, and checked its same three axioms.

The retained LeanCert task is exactly **10500<11000**, constant 10500 on the singleton [0,0], bound 11000, precision −53 and depth 10. It participates in the strict comparison chain. It is a simple scalar separation, not interval verification of a matrix root or singular value. All matrix certificates and all analytic bridges are supplied by the exact Lean proof. No native runtime oracle, custom axiom, hidden assumption, unsafe implementation or admission was found. A lexical scan is retained as a supplement, not substituted for the actual axiom/dependency audit.

Mathlib is pinned at `0df444a360eaa60ab8c11dca51a86af692955474`; LeanCert at `621a43d7cf21f87872392a01e874f2f1dbddc926`. Actual inspected library files were compared with their immutable Git objects and hashed in `inspected-library-sources.json`.

## Review standards, attribution and disposition

I applied the NLA adaptation of Tau Ceti's correctness, scope, proof-quality, reuse, generality and attribution rubrics at `afb424eda89e8ac96d9eb69f6a88972055a4cd1b`, rechecking the cached rubric/tree hashes. This is not official Tau Ceti endorsement. The code advances one complete permanent target. Generic CFC, singular-value, positivity and norm APIs are reused; the focused pinned-library search is retained. The short bridge lemmas have direct consumers, and the finite certificate blocks are readable exact computations. The explicit wrapper/coercion steps expose genuine CFC and Euclidean semantics, rather than assuming accidental alternative norms. Three squarings and a single tested row avoid unnecessary root approximation or interval subdivision.

Matthew J. Colbrook retains mathematical attribution for the original resolution and method. The adapted rational witness and formalization are disclosed. George Stepaniants is credited with the Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA affiliation, without a contact email. Neighboring campaign proof organization and the Mathlib/LeanCert sources are acknowledged. No source-author endorsement, human peer review, novelty or complete parameter classification is claimed.

**Remaining publication requirements:** combine this review with the separately recorded second independent final approval, prepare a truthful candidate README/manifest, complete actual Linux sandboxed Comparator/default-kernel execution and controls, then obtain the independent operational audit and publication review. The frozen README's historical statement-stage “no proof” sentence must be archived and replaced during candidate packaging; the mathematical review does not alter it. Historical phase language in frozen numerical/source-mapping records should remain labeled historical. Canonical status remains Solved. I edited no frozen mathematical/configuration/canonical file and made no commit or push.

Raw commands, fresh artifacts/log hashes, exact computations, safety/signature checks, proof-term inspection and all input identities are under `proof-referee-1-evidence/`. Its manifest binds this report and every retained review artifact.
