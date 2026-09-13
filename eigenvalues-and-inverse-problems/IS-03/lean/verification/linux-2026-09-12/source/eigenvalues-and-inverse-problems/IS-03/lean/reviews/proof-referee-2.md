# IS-03 independent final proof referee 2

**Verdict: APPROVE — complete proof of all seven frozen contracts, including the full original conjecture's negation.** This is an independent AI-agent mathematical and local Lean review. Actual sandboxed Linux Comparator and independent default-kernel replay remain **pending**; this approval does not authorize a Lean-verified status by itself.

Reviewer: `/root/formal_review_standards`, a Codex agent. I did not author the IS-03 statements or implementation. I previously served as statement referee 2 and contributed to the campaign's shared verification infrastructure; neither role substitutes for the fresh checks here. Root and `/root/solved_statement_inventory` coauthored the implementation. The other independent final referee has separate evidence. Review performed on 12 September 2026, America/New_York; exact UTC execution times are retained below.

## Exact reviewed inputs and checks

The approved proof freeze is [verification/proof-freeze.json](../verification/proof-freeze.json), SHA-256 `636cdb024f5b73ea61edd518de39ee192a604987aad2b9914c4d7e7eeab672e4`. I checked all **203 frozen project files**, all **34 earlier statement inputs**, both statement approvals and their implementation gate, and all **10 original source Git blobs** at base `f41f1f9ffa2171550d4bb795862c6170c4f26070`. They remain unchanged. [Reviewed inputs](proof-referee-2-evidence/reviewed-inputs.json) records the complete identities.

Key SHA-256 identities:

| Input | SHA-256 |
| --- | --- |
| Definitions | `8b4b581e9831b0438d0635b013a60df0cf0139fa9087850b842d8e58975ea1a9` |
| Challenge | `4a8817f7c983819fac0a9206092831e72709fcfdb73b0687350914162ef23440` |
| Newton | `451953080999a9b7aec73af27af178018fec6d340439c3b4081716165a7f1ddd` |
| Proof | `39c6be952b030622404a216c625d86404a579dc8a6c992a268a7bdf10ea30c28` |
| Solution | `1b3d7ebe1fabc51a04c3012c694f4bd52efe654ebb933e273b87153b267d7508` |

My **11 fresh Lean commands** passed: all eight proof modules from Definitions through Solution, my own actual-term inspector, the separately loaded Challenge, and an additional literal-certificate kernel replay. There were **18 candidate plus 15 independent kernel trust/axiom checks**, all using only the standard three axioms or subsets. Challenge alone reported its seven deliberate reference holes; no proof module or independent check produced a warning. Solution does not import Challenge.

The run used Lean 4.33.1 in a new initially empty prefix, excluding every previous IS-03 and MI-22 project object directory. It reused only matching dependency objects from the read-only MI-22 cache. All ten dependency source pins and clean Git states were checked before and after, including LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. No Lake invocation, dependency rebuild, download or dependency copy was used. [Environment](proof-referee-2-evidence/environment.json), [commands](proof-referee-2-evidence/fresh-checks.json), [axioms](proof-referee-2-evidence/axioms.json), [certificate replay](proof-referee-2-evidence/certificate-result.json), and [final integrity](proof-referee-2-evidence/final-integrity.json) distinguish this macOS check from the required future Linux execution.

## Full target fidelity

I read the complete canonical target, unchanged original and authored source proof, source correspondence and numerical plan, then all actual Definitions, Challenge and implementation modules. The original manuscript identity is `548553e2f177da2a2c5135030c6a34fff761d2b9c800b246b7f9a6797e02d45c`.

`DerivativeRealizabilityConjecture` retains every real entrywise-nonnegative matrix of every natural order at least five, and requires a real entrywise-nonnegative realization of **exactly** order `n - 1`. The equality is between genuine real characteristic polynomials, with the actual formal derivative scaled by the reciprocal of the original order. Entrywise nonnegativity is the real entry order; it is not positive-semidefinite order. Powers use matrix multiplication, and trace is the sum of actual diagonal entries. The characteristic matrix is `XI - A`.

The final theorem negates that complete assertion at the unchanged order-seven witness `diag(1/2,C₂,C₄)`. No symmetry, diagonalizability, real-spectrum, irreducibility, invertibility or zero-trace assumption is added. In particular, `trace_moment_certificate` requires only the actual characteristic-polynomial equality for an arbitrary real order-six matrix, not nonnegativity or a supplied moment identity. Every numerical identity is proved. The seven Solution headers match the seven frozen Challenge headers exactly apart from whitespace, and all seven exports are actual theorem declarations. Comparator selects these names with **no definition exceptions** and precisely the standard-three axiom whitelist.

The stronger informal zero-padding exclusion, separate moment-conjecture consequence and smallest-order or historical-priority questions are outside the exports. Excluding those ancillary claims does not weaken the original exact-order target.

## Mathematical proof audit

1. **Admissibility and actual characteristic polynomial.** `Matrix.pow_apply_nonneg` and the finite diagonal sum prove nonnegative powers and traces generically, including dimension zero and exponent zero. The concrete witness has all 49 entries checked and genuine trace `1/2`. An explicit equivalence reindexes the actual matrix into a three-plus-four block matrix. Actual determinant identities for the blocks prove `(X-1/2)(X²-1)(X⁴-1)`; no characteristic polynomial is stipulated by definition. Formal differentiation and exact polynomial extensionality prove the displayed monic degree-six polynomial `q`.

2. **Derived spectral properties.** The two explicit Bézout polynomials in `Algebra.lean` satisfy `a*q + b*q.derivative = 1`. The actual imported definition of separability is this coprimality condition. Over the complex numbers, separability and splitting give exactly six distinct roots. For every real `B` with characteristic polynomial `q`, its actual complexified linear map has a nonzero eigenvector at each of those roots. Distinct eigenvalues imply linear independence; the exact cardinality/finrank equality supplies a basis. Diagonalizability is therefore **derived from the proved property of q**, never an additional premise on B. Using a root set here does not lose multiplicities: separability has been proved, cardinality is six, and the full polynomial product is subsequently proved.

3. **Actual powers and traces.** `root_product_and_trace` proves the diagonal matrix of each natural power in that genuine eigenbasis. `Matrix.toLin'_pow`, matrix-map powers, basis-independent trace and characteristic-polynomial transport connect this matrix back to the original real `B`. The proof obtains both the complete product of linear factors and every actual power trace. The trace identity is not checked only on a companion matrix, postulated as an interface assumption, or inferred from an unproved eigenvalue enumeration.

4. **All seven exact moments.** The Newton module evaluates Mathlib's actual multivariate Newton identity at any finite family of six complex values. Vieta's formula identifies the elementary symmetric functions from the full polynomial product. Indices retain repetitions; this helper has no distinctness hypothesis. The seventh elementary symmetric term vanishes because a six-index family has no seven-element subsets. The seven finite recurrences give exactly `3/7`, `79/49`, `48/343`, `6731/2401`, `5213/16807`, `219766/117649`, and `-8593/823543`. Injectivity of the real-to-complex map returns these to the genuine real matrix traces.

5. **Material contradiction and complete conclusion.** The hypothetical nonnegative realization's seventh trace equals the frozen negative value, while the generic power theorem makes it nonnegative. The actual final proof uses the negative-moment certificate and then instantiates the full universal conjecture at order seven. I checked the elaborated consumer chain, rather than relying on an unused numerical theorem's presence.

My separate Fraction/AST diagnostic parsed the actual Lean matrix, polynomials, moments and both implemented Bézout polynomials. It independently verified the sparse determinant, normalized derivative, seven Newton values and seven actual companion power traces; the supplied Bézout identity agrees with an independently generated Euclidean identity. Its integer form for `7q` has coefficients of at most 22 bits. Repeated-value and zero families also satisfy the seven generic Newton sign conventions in the supplementary diagnostic. These finite checks support transcription review; they are not the universal Lean proof. See [reconstruction](proof-referee-2-evidence/reconstruction.json).

## Trust, LeanCert and computation reduction

My [inspector](proof-referee-2-evidence/Inspect.lean) traversed types and bodies from all seven exports, checked **61 actual project declarations**, rejected project axioms and unsafe declarations, and required **40 material dependencies** from the actual Mathlib and LeanCert implementation. From the full negation alone, the traversal reaches **55** project declarations. All relevant actual signatures and proof terms are retained in [Inspect.log](proof-referee-2-evidence/Inspect.log); imported API identities and Git blobs are in [primary API inputs](proof-referee-2-evidence/primary-api-inputs.json).

The actual scalar proof calls `verify_strict_upper_bound_dyadic_checked` on the constant expression `(-8593)*(1/823543)`, at dummy interval `[0,0]`, strict upper bound zero, dyadic precision `-53` and Taylor-depth parameter `10`. There is no variable interval subdivision or numerical root calculation. Taylor depth does not create approximation work for these rational constants. Explicit kernel mode has no native fallback. I inspected the pinned validity theorem, checked the exact retained helper's type, and independently recomputed that same Boolean proposition with `decide +kernel`.

The retained path is:

```
not_derivativeRealizabilityConjecture
→ not_derivativeRealizabilityConjecture_proved
→ counterexample_proved
→ negative_moment_proved
→ numerical_negative_moment
→ numerical_negative_moment._proof_1_7
```

[Consumer-chain evidence](proof-referee-2-evidence/consumer-chain.json) checks every edge from the actual elaborated environment. The scalar certificate is small and materially consumed; it is not an interval decoration standing in for the matrix argument. Largest direct determinant expansion is order four. Reusing exact polynomial identities and the generic spectral/Newton APIs avoids root approximations, full order-seven determinant enumeration and exhaustive matrix search.

## Tau Ceti angles, documentation and limitations

I applied the repository's adaptation of the ten [Tau Ceti Review rubrics](https://github.com/TauCetiProject/TauCetiReview/tree/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/rubrics): correctness, scope, proof quality, reuse, generality, API, naming, placement, documentation and attribution. This is not an official Tau Ceti runner result or endorsement. [Standard identities](proof-referee-2-evidence/review-standard-inputs.json) and [bounded reuse searches](proof-referee-2-evidence/reuse-searches.json) are retained.

The implementation reuses genuine library results and exposes the fixed target contracts. The evaluated Newton helpers have actual consumers; the private cycle-block helpers are specific to this witness. The three-plus-four block decomposition, explicit local complexification and sequential elementary/power-moment calculations make the necessary coercion and polynomial bridges reviewable. I found no material API duplication, opaque replacement of a prerequisite, unneeded speculative generalization or mathematical scope drift. The fixed Challenge-facing wrappers are the repository's review boundary, not obsolete compatibility aliases.

**Publication preparation remains:** the frozen live README still describes the statement-only stage. Archive those exact historical bytes and refresh the live README and metadata to the completed proof and these final reviews before preparing the Linux candidate. `NUMERICAL_TARGETS.md` and the copied “planned certificate” reference comment are historical statement-stage records; the actual proof and proof map resolve those obligations. They should not be presented as current incomplete mathematics. This documentation update requires no mathematical change and is outside the frozen-proof edits of this review.

The source retains Matthew J. Colbrook's mathematical credit and Johnson/Hoover–McCormick–Paparella–Thrall attribution. Formalization credit correctly names George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI assistance disclosed. No George email is introduced; the source manuscript is not relicensed or reassigned by the new Apache-licensed code.

Two reviewer-preparation corrections are transparently retained: an initial cache assertion incorrectly required an object directory for unused Cli, and the independent parser initially handled `C(…)` but not Lean's bare `C 544126` syntax. Both failed before their respective proof/arithmetic checks; neither required changing a mathematical input, weakening a proof assertion, changing a dependency, or rebuilding anything. Corrected independent checks passed. Initial scripts and explanations remain in the evidence.

No frozen proof, definition, pin, configuration, source, canonical status or Git history was modified. This review does not claim an exhaustive literature/novelty search, external human peer review, complete independent auditing of Lean/Mathlib, or an unobserved Linux run. The exact evidence is sealed in [EVIDENCE-MANIFEST.json](proof-referee-2-evidence/EVIDENCE-MANIFEST.json).
