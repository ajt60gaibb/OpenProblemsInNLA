# MI-26 independent final proof referee 2 — PASS

Date: 12 September 2026. Reviewer: OpenAI Codex agent `/root`, independent of implementer `/root/leancert_examples`. **Approve the frozen complete mathematical proof for subsequent Linux verification. No mathematical correction is requested.** This is independent AI-agent review, not external human peer review or an operational Linux verdict.

I read the complete canonical target, Colbrook's complete source manuscript, all frozen Definitions and Challenge signatures, the entire Proof and Solution, and the actual pinned Mathlib definitions and theorems on which the semantic bridges depend. Both independent statement approvals preceded implementation. All 21 files in the author's proof freeze, including those approvals and the three statement files, remain byte-for-byte unchanged. The canonical source and its mathematical attribution remain unchanged.

## Mathematical fidelity and proof

The final declaration negates the exact original assertion for every positive dimension, arbitrary complex positive semidefinite A and B, and every real-valued concave function on the nonnegative half-line satisfying f(0)≥0. Both complex unitaries are existentially quantified after those inputs. The order is genuine matrix PSD order of right minus left. No positive-definiteness, commutation, global nonnegativity, monotonicity or continuity restriction has been introduced. The rational dimension-two witness suffices for the complete universal negation. The source's separate stronger positive-definite construction is outside these exports.

The first generic bridge proves both directions of the canonical scalar concavity definition. Mathlib's two nonnegative weights summing to one correspond exactly to θ and 1−θ, and convexity of the fixed half-line is automatic. The concavity witness is the analytic Jensen-gap identity θ(1−θ)(x−y)²≥0, for all real x,y and allowed weights, so it certainly covers the required half-line. The exact polynomial has f(0)=0 and f(2)=−2; the latter usefully records why this proof concerns the allowed real-valued class rather than the narrower nonnegative-valued class.

The second generic bridge proves that the actual real `cfc` in the complex matrix algebra equals the complete spectral expression with Mathlib's genuine eigenvalues and eigenvector unitary. I inspected `Matrix.IsHermitian.cfc_eq` and its proof: no continuity of f on the whole half-line is required because a Hermitian matrix has finite spectrum. The implementation's `using!` transports the same matrix value across definitionally related instances; it does not assert a new identity or replace the functional calculus. Fresh elaboration prints the actual proof and all public types.

The third generic bridge proves that changing f outside the nonnegative half-line has no effect at any PSD matrix. It uses the actual nonnegativity of every Hermitian eigenvalue of a PSD matrix and equality on the half-line. Thus the choice to represent the original half-line function by a function on all real numbers does not restrict the target: every half-line function has an extension, and its negative values are irrelevant. The fourth bridge proves actual polynomial CFC equals A−A² for every Hermitian A using the genuine CFC subtraction, power and identity theorems. This is a generic semantic identity, not a witness-specific replacement definition.

The two rational witness matrices are proved PSD as actual outer products of (1,0) and (3/5,4/5). Exact complex matrix multiplication proves their projection identities. The polynomial CFC bridge therefore gives f(P)=f(Q)=0 and

f(P+Q) = [[−18,−12],[−12,0]]/25.

These entries and the nonzero vector w=(1,−2) match my independently reconstructed rational data at the unchanged statement boundary. Exact multiplication proves w* f(P+Q) w = 6/5. The implementation never substitutes an unproved root table or a sampled spectral value.

For every pair of complex unitaries, both terms on the proposed right-hand side vanish because the two individual CFC values are zero. Assuming the original matrix inequality therefore makes −f(P+Q) PSD. Applying its genuine complex quadratic-form nonnegativity to w and taking the real part yields 0≤−6/5. The explicitly retained kernel LeanCert certificate 0<6/5 contradicts this. Finally, instantiating the original fully quantified conjecture at dimension two, P, Q and the admissible polynomial produces exactly the excluded unitary pair. No extra witness assumptions remain in the final negation.

## Independent execution and certificate retention

I compiled Definitions, Proof and Solution sequentially into a fresh root-referee artifact prefix. All three commands exited zero, without warnings or errors. Eight selected internal declarations and all seven public declarations passed their kernel trust assertions. The 15 fresh axiom lists are each exactly `{propext, Classical.choice, Quot.sound}`; dependencies of these declarations are checked transitively. This count is not a claim that each separate internal lemma has its own printed assertion. All seven public headers match the frozen Challenge after comment removal and whitespace normalization. Comparator permits no definition replacement names and only those three axioms.

My separate read-only inspection traverses actual project proof dependencies starting at the public conjecture negation. It visits 34 reachable project declarations, including generated auxiliaries. The scalar certificate is on that dependency path, and its actual body retains `LeanCert.Validity.verify_strict_upper_bound_dyadic_checked`. Hence LeanCert is consumed by the mathematical contradiction, not merely imported or invoked for an unused lemma. Its point calculation uses the singleton interval [0,0]. There is no interval subdivision, numerical matrix-root computation, eigenvalue approximation or search over unitaries.

The inspection log SHA256 is `95131658cda00c1296eb8ec92e5341e92791c43a369200a377edfcc8e8417f35`. Exact commands and outputs, before/after source identities, both statement approvals, the 21-file freeze check, signature comparison, supplementary source scan, library hashes, actual dependency identities and the reproducible inspection scripts are retained in [proof-referee-2-root-evidence](proof-referee-2-root-evidence/). Its manifest SHA256 is `1eaea043e562e28d23a6253946569498af51956cbd670a2ebce010f3444d1746`.

All ten dependency Git HEADs match the locked manifest and have clean tracked source. The project pins Lean v4.33.1, LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. These checks ran on macOS arm64 and reused matching dependency artifacts. They are not a source rebuild of Mathlib or an actual Linux Comparator/default-kernel replay. Challenge's seven deliberate placeholders remain confined to the separate template and are absent from Solution's import graph.

## Scope and remaining gates

I applied the relevant Tau Ceti faithfulness/correctness, scope, computation, reuse and attribution rubrics at `afb424eda89e8ac96d9eb69f6a88972055a4cd1b`, adapted to the complete permanent MI-26 target. Actual Mathlib CFC and PSD APIs are reused without dependency modifications. Exact projections and a single scalar quadratic-form obstruction eliminate all numerical spectral work while preserving every original quantifier. No official Tau Ceti endorsement or external human approval is asserted.

Mathematical counterexample credit remains Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Formalization credit is George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI assistance and without George's email.

Referee 1's separate final approval, truthful metadata and actual Linux Comparator/default-kernel replay remain distinct publication gates. No canonical promotion, commit or publication was performed by this review. A substantive mathematical change reopens the affected reviews.

| Frozen file | SHA256 |
| --- | --- |
| `NLA/MI26/Definitions.lean` | `821cb1b2a29f7382a1f36bd6b506bc6b249b9da0b61837702658173814995f63` |
| `Challenge.lean` | `85eafac2fc875ddacb35c37f832834cfe79e6b10730f2656185209592f608fe1` |
| `NUMERICAL_TARGETS.md` | `ecc403bb0f57fc49f2e3be78c9012f7e606ca8035d92af83fa95bddfbe994257` |
| `NLA/MI26/Proof.lean` | `94dd1dde3f1b12002380ae4730ea6396a955f7cbe69a34dde101e7a035fae0af` |
| `Solution.lean` | `a79aa8df0b6b7501dcb6d264fc8a9a21ac0710aa05ed65bff3b244ba97fe6da1` |
