# IS-03 independent statement referee 1

**Verdict: APPROVE the frozen statement boundary.** No mathematical statement correction is requested. This is a statement review, not a completed-proof, Linux, Comparator, or publication approval. All seven Challenge declarations remain intentionally unproved.

Reviewer: `/root/leancert_examples`, 12 September 2026. I authored neither this statement package nor a proof implementation. The statement authors are `/root` and `/root/solved_statement_inventory`; neither is counted as this independent referee. Proof implementation must wait for the other independent statement approval and the recorded parent gate.

## Exact reviewed identity

The project is `/tmp/nla-lean-is03-worktree/eigenvalues-and-inverse-problems/IS-03/lean`. I received the sealed handoff before compiling any project statement. All **34 frozen project files** and **10 original source files** passed independent SHA-256 verification before and after the fresh checks. Each original source also matched its exact Git blob at upstream `f41f1f9ffa2171550d4bb795862c6170c4f26070`. `Proof.lean` and `Solution.lean` were absent throughout this review. I changed no frozen file, canonical page, metadata, status, index, commit or remote.

| Reviewed input | SHA-256 |
| --- | --- |
| `reviews/statement-freeze.json` | `588196a54decb127a814dc4860621505d6874a077295f3e30a782d7f28b8ac6c` |
| `reviews/statement-handoff.md` | `3c1d998ba3d3a658a7d9ea706e4357ab3587757050cef70e6f366481affd7c68` |
| `NLA/IS03/Definitions.lean` | `8b4b581e9831b0438d0635b013a60df0cf0139fa9087850b842d8e58975ea1a9` |
| `Challenge.lean` | `4a8817f7c983819fac0a9206092831e72709fcfdb73b0687350914162ef23440` |
| `NUMERICAL_TARGETS.md` | `b1fe777e2d4853b4d60d75e4d0628939f19434434ca82ac4ffe2a3e5bdbf1787` |
| `SourceCorrespondence.md` | `596109711f49f216bf6b14a4c37d86402020aeefd2e8468d8b60dcafe045a112` |
| `comparator.json` | `f1e84761b1175d1d638b6cc26c2c2797c7da64ca7dd73919594437388484bf0a` |
| `source-inputs.json` | `dec263f906d2dbbaa2351e3efa20a60398b8bf1ae8a40cbf446d348a80530e40` |

My [23-file evidence manifest](statement-referee-1-evidence/EVIDENCE-MANIFEST.json) has SHA-256 **`71c1789f34770665834324143edd1a8dad5a55531404be24e2b309a0e30dd964`**. It binds the independent scripts, inspection source, raw logs, exact diagnostic, clean-pin records, source/rubric correspondence and final integrity receipt. Only that outer manifest itself is excluded from its file accounting.

## Full source and target correspondence

I read the complete canonical README and problem TeX, both authored textual solution formats, the full original reviewed manuscript, the complete informal review, submission/preservation records, the mathematical-section hash record, and all definitions, Challenge signatures, numerical targets, correspondence and handoff. After writing and running my own independent exact calculation, I inspected the IS-03 section of the supplied multi-problem checker as a diagnostic; I did not import or run it. No new PDF rendering or priority survey is claimed.

I also independently read the primary paper's printed page 2. Its definition uses the same matrix order as the eigenvalue list, including multiplicities, and Johnson's conjecture imposes no symmetry, diagonalizability, irreducibility or trace-zero restriction. Its low-order statements are established special cases. This supports the canonical target's unrestricted remaining `n ≥ 5` formulation. [Hoover–McCormick–Paparella–Thrall, Conjecture 1.2](https://arxiv.org/pdf/1712.05454).

The frozen conjecture quantifies over **every natural `n ≥ 5`** and every real entrywise-nonnegative `n × n` matrix `A`, and asks for an entrywise-nonnegative real matrix of **exactly order `n - 1`** whose genuine characteristic polynomial is the genuine formal derivative of `A.charpoly` scaled by the real reciprocal of `n`. Equality is in `Real[X]`, not equality on sampled points or equality of sets without multiplicities.

No normality, diagonalizability, symmetry, positive-semidefinite condition, simple-root, invertibility, irreducibility or zero-trace assumption is inserted. The order-seven source witness has trace one half and is reducible; both features are allowed. The final contract negates the complete original conjecture. The manuscript's stronger statement about arbitrary zero padding, its separate moment-conjecture consequence, and minimal-order or priority claims are explicitly outside the formalization exports. Their exclusion does not weaken the original exact-order target.

## Actual definitions and adversarial boundary checks

The fresh elaboration was inspected in full, including `pp.all` output for the conjecture, normalized derivative, nonnegative-power contract, arbitrary-matrix trace contract and concrete counterexample. It confirms:

- `RealMatrix n` is `Matrix (Fin n) (Fin n) Real` with the ordinary real field. `EntrywiseNonnegative` means `∀ i j, 0 ≤ A i j`, rather than a matrix order or a spectral condition.
- `A ^ k` uses the actual `Matrix.semiring` natural-power instance. Ordinary matrix multiplication uses the finite sum of products; it is not entrywise exponentiation.
- `Matrix.trace` is the actual sum of diagonal entries. The generic nonnegative-power statement includes every natural `k`, including zero. At power zero the identity matrix has trace `n`. At dimension zero the trace is zero and the entry predicate is vacuous, which is a valid harmless generalization; the original conjecture still excludes that dimension.
- `Matrix.charpoly` is the actual determinant of `Matrix.charmatrix`, and that matrix is `XI - C(A)` over real polynomials. The empty characteristic determinant is one. No separate polynomial is defined to be a matrix's characteristic polynomial.
- `normalizedDerivative` applies Mathlib's actual formal polynomial derivative and real scalar multiplication by `(n : Real)⁻¹`. The real denominator is nonzero whenever the conjecture's `n ≥ 5` premise applies. Totalization at `n = 0` cannot affect the original target.
- The matrix witness has precisely the 49 entries in the manuscript. The proposed `p`, explicit `q`, and the trace-value table are separate data; their semantic equalities are required theorem conclusions.
- `trace_moment_certificate` has arbitrary `B : RealMatrix 6` and **only** `B.charpoly = derivativePolynomial` as a premise. It does not even assume nonnegativity. All seven actual trace values are conclusions. The indexing `i.val + 1`, for `i : Fin 7`, covers powers one through seven; the literal `6 : Fin 7` selects the seventh moment.

The arbitrary-matrix premise is not an inconsistent shortcut: my independent exact calculation constructs a real companion matrix whose genuine characteristic determinant is `q`. Its negative entries are permitted by the trace-certificate contract. The future impossibility theorem must exclude all nonnegative realizations by the universal trace bridge, not by testing only this companion.

## Independent exact reconstruction

My standard-library `Fraction` diagnostic parsed the actual frozen matrix, polynomial coefficients and moment table and checked the source matrix independently. A sparse determinant expansion avoids an unnecessary enumeration of all order-seven permutations. It yields

\[
 p=(X-\tfrac12)(X^2-1)(X^4-1),\qquad
 q=\frac{p'}7=X^6-\frac37X^5-\frac57X^4+\frac27X^3-\frac37X^2+\frac17X+\frac17.
\]

The explicit `q` is monic of degree six. Independent Newton recurrence gives:

| Power | Moment |
| --- | --- |
| 1 | `3/7` |
| 2 | `79/49` |
| 3 | `48/343` |
| 4 | `6731/2401` |
| 5 | `5213/16807` |
| 6 | `219766/117649` |
| 7 | `-8593/823543` |

The recurrence `7s₇ = 3s₆ + 5s₅ - 2s₄ + 3s₃ - s₂ - s₁` has numerator contributions `659298, 182455, -659638, 49392, -189679, -50421` over `7⁶`; these sum to `-8593`, and the final denominator is `7⁷ = 823543`. I separately computed the companion's characteristic determinant and its first seven matrix powers. Their traces agree with every entry of the table. The actual empty determinant/trace and identity-matrix zero-power boundaries were checked as exact diagnostics.

[The diagnostic record](statement-referee-1-evidence/reconstruction.json) retains the full matrices and rational results. These finite calculations validate transcription and arithmetic. They are not a Lean proof of the arbitrary-real-matrix trace theorem, and no numerical roots or floating-point eigensolver were used.

## Fresh statement checking and trust scope

Three independent direct Lean commands passed: fresh Definitions, fresh Challenge, and my semantic/definition inspector. Only the seven intended Challenge `sorry` warnings occurred; Definitions and inspection produced no warnings. The [fresh command record](statement-referee-1-evidence/fresh-checks.json) includes the source and object hashes, exact arguments, complete `LEAN_PATH`, timestamps, durations, exit codes and raw logs.

The run used Lean **4.33.1**, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, on macOS ARM64, with a new prefix ending `is03-statement-referee1-4oynkvzs`. It used the ten clean, exactly pinned MI-22 dependency repositories and available objects **read-only**. It excluded old IS-03 and MI-22 project objects. No dependency tree was copied or rebuilt; Lake, Linux and Comparator were not run.

All **twelve concrete definition-only** LeanCert kernel/axiom checks passed and reported only `propext`, `Classical.choice`, and `Quot.sound`. They cover the eight project definitions and the genuine characteristic polynomial, characteristic matrix, trace and formal derivative. They do not certify any admitted Challenge theorem. The actual pretty-printed Challenge proof terms visibly retain their expected `sorryAx` placeholders.

`comparator.json` lists exactly the seven declared contracts, no replaceable definition names and only the standard three permitted axioms. `Solution` is already registered in the pinned Lake file while the default remains `Challenge`; its implementation is absent. No native execution or custom-axiom permission is granted by this review.

I approve the proposed **material, explicit kernel LeanCert singleton certificate** for `(-8593/823543 : Real) < 0`. It must be retained in `negative_moment` and consumed in the seventh-trace contradiction and complete negation. No scalar interval certificate has been executed in this statement stage. It cannot substitute for the matrix, determinant, polynomial, derivative, or universal trace proofs.

The primary Mathlib definitions and relevant boundary APIs were read at the pinned source. In particular, `trace_eq_sum_roots_charpoly` preserves the characteristic-root multiset over an algebraically closed field; applying it to `B^k` alone does **not** establish that the roots are powers of those of `B`. If roots are used, their transport and multiplicities must be proved. The documented alternative of an exact matrix/characteristic-coefficient recurrence is also acceptable if fully proved. No diagonalizability or separability shortcut may become a new premise; any special property of this concrete `q` must be derived. [Source/API identities](statement-referee-1-evidence/api-source-inputs.json) bind the inspected files.

## Adapted referee standards and conclusion

All ten pinned Tau Ceti angles were applied at their **statement-review scope**, through the repository adaptation. [rubric-inputs.json](statement-referee-1-evidence/rubric-inputs.json) binds the source rubrics at `afb424eda89e8ac96d9eb69f6a88972055a4cd1b` and the local protocol. This is not an official Tau Ceti service result.

| Angle | Statement-stage finding |
| --- | --- |
| Correctness | PASS: exact definitions, quantifiers, arithmetic and fresh elaboration agree; no proof completeness is asserted. |
| Scope | PASS: full original all-order exact-dimension negation is retained. |
| Proof quality | Obligations are explicit; the universal trace bridge remains substantive future work rather than an assumption. |
| Reuse | Actual Mathlib primitives and relevant available APIs are identified honestly. |
| Generality | Generic nonnegative powers include valid zero cases; the counterexample requires only the original order-seven instance. |
| API design | Seven contracts separate generic semantics, witness, polynomial identities, universal trace data, scalar sign and full resolution. |
| Naming | Names and all indices correspond to their actual roles in `NLA.IS03`. |
| Placement | Definitions, isolated Challenge and future Solution are separated; original sources remain intact. |
| Documentation | Current statement-only status, unproved bridge, cache reuse and later gates are stated accurately. |
| Attribution | Colbrook's mathematics and George's formalization credit are distinct and preserved. |

Matthew J. Colbrook retains mathematical authorship. George Stepaniants receives the approved formalization credit with the **Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA**, and AI assistance disclosed. No George email was added; original source metadata was left unchanged.

I am satisfied that these exact statements specify the complete intended negative resolution without vacuous strengthening or a changed mathematical target. The approval binds the frozen bytes above. Any mathematical boundary change requires renewed independent review. Complete proofs, two independent final proof reports, actual Linux/default-kernel/Comparator verification and controls, operational audit, and publication metadata remain later gates.
