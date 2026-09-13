# IS-03 independent final mathematical referee 1

**Verdict: APPROVE the complete frozen mathematical formalization. No mathematical correction is requested.** This is a local independent proof review. Actual Linux Comparator/default-kernel verification, operational review and publication remain separate gates.

Reviewer: `/root/leancert_examples`, a Codex AI agent, 12 September 2026. I authored neither the statements nor the proof. The coordinator and `/root/solved_statement_inventory` coauthored the implementation and do not count as its independent final referees. My earlier independent statement approval remains unchanged. I inspected the complete original target and source, all seven actual proof modules and Solution, both statement approvals, the author freeze and the actual primary-library interfaces. I used my own initially empty project prefix and independently reconstructed the finite data; the author's green build or companion calculation is not the basis of this verdict.

## Frozen identity and fresh evidence

| Reviewed input | SHA-256 |
| --- | --- |
| `verification/proof-freeze.json` | `636cdb024f5b73ea61edd518de39ee192a604987aad2b9914c4d7e7eeab672e4` |
| `reviews/proof-completion.md` | `534e662eda86b3aee5bc1bfcf07fc1d0b8d0040c63c9c9f45e162e8412f428ea` |
| `NLA/IS03/Proof.lean` | `39c6be952b030622404a216c625d86404a579dc8a6c992a268a7bdf10ea30c28` |
| `Solution.lean` | `1b3d7ebe1fabc51a04c3012c694f4bd52efe654ebb933e273b87153b267d7508` |
| `reviews/statement-freeze.json` | `588196a54decb127a814dc4860621505d6874a077295f3e30a782d7f28b8ac6c` |

All **203 frozen project inputs**, **34 original statement inputs**, and **ten original source files** remain byte-identical. Each original also matches its exact Git blob at `f41f1f9ffa2171550d4bb795862c6170c4f26070`. The two independent statement approvals were present before implementation, as recorded in the preserved proof-start evidence. I changed no mathematical source, configuration, pin, canonical page, status, registry, commit or remote.

My ten fresh commands independently elaborated Definitions, Algebra, Spectral, Witness, Newton, Numerical, Proof, Solution, the isolated Challenge, and my inspection module. All returned zero. Candidate sources and inspection had no warnings; Challenge had exactly its seven intentional reference holes. An **eleventh** command printed the actual retained scalar checker and independently proved its same Boolean equality using `decide +kernel`. The exact commands, full `LEAN_PATH`, initially empty output prefix, source/object/log hashes, exit codes and timings are in [the evidence directory](proof-referee-1-evidence/).

The local platform is macOS ARM64, Lean **4.33.1**, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. Ten clean exact pinned MI-22 dependency repositories and objects were reused **read-only**. All prior IS-03 and MI-22 project objects were excluded. No dependency copy, download, complete dependency-source rebuild, Lake invocation, Linux run or Comparator execution is claimed by these local commands.

## Full original target and every contract

The canonical question retains every natural order `n ≥ 5`, every real entrywise-nonnegative matrix `A` of that order, and a possible entrywise-nonnegative real realization `B` of **exactly order `n - 1`**. Its actual characteristic polynomial must equal the actual formal derivative of `A.charpoly` scaled by the real reciprocal of `n`. The final theorem negates this whole universal assertion. No symmetry, diagonalizability, irreducibility, invertibility, normality, simple-spectrum, real-spectrum or trace restriction is added to it.

The definitions are ordinary Mathlib matrices over `ℝ`, ordinary matrix multiplication/powers, finite diagonal-sum trace, `det(XI - A)` characteristic polynomial, formal polynomial derivative and real scalar multiplication. Neither a proxy polynomial nor a finite diagnostic is defined to be the answer. The fresh `pp.all` inspection retains the actual arbitrary-real-`B` signature: its only premise is `B.charpoly = derivativePolynomial`. Even nonnegativity is absent from this trace-moment premise.

All seven Solution signatures match the approved Challenge signatures exactly after whitespace normalization and independently elaborate. Comparator selects those same seven names with **no definition exceptions** and only the three permitted axioms:

| Export | Complete mathematical content reviewed |
| --- | --- |
| `nonnegative_power_trace` | Every natural power of every real entrywise-nonnegative square matrix has nonnegative entries and trace, including dimension and power zero. |
| `witness_admissible` | The unchanged actual order-seven matrix is entrywise nonnegative and has actual trace `1/2`. |
| `witness_polynomials` | Its genuine characteristic polynomial and normalized formal derivative equal the displayed polynomials; the derivative is monic of degree six. |
| `trace_moment_certificate` | Every real order-six matrix whose actual characteristic polynomial is the derivative has all seven exact power traces, with no additional spectral premise. |
| `negative_moment` | Index six in `Fin 7` gives exactly `-8593/823543`, and this value is strictly negative. |
| `counterexample` | No entrywise-nonnegative real order-six matrix realizes the actual normalized derivative of the admissible source matrix. |
| `not_derivativeRealizabilityConjecture` | Unconditional negation of the entire original universal conjecture. |

The original stronger no-zero-padding claim, separate moment-conjecture consequence, minimal-order issues and priority claims remain outside these exports. None is needed for the complete exact-order negative answer. The source's reducible positive-trace witness is allowed by the original target. Its original unrestricted meaning was also independently checked against the primary paper at the earlier statement gate; no new literature or priority search is claimed here.

## The unrestricted matrix-to-trace bridge

The substantive obstacle from both statement reviews is now discharged by actual proofs, rather than assumed or delegated to a companion matrix.

`Algebra.lean` proves the separability of the **actual concrete polynomial** `q` using a complete Bézout identity. In `Polynomial.separable_def'`, the obligation is genuinely `a*q + b*q.derivative = 1`. Both displayed rational-coefficient polynomials are supplied and that exact polynomial identity is proved. My independent `Fraction` script parses every new signed integer coefficient and confirms the identity separately. The largest integer coefficient has 22 bits. No root approximation or numerical separability test is used.

`complexRoots_card` applies the genuine separability-and-splitting cardinality theorem. I read its pinned implementation: it passes through the root **multiset**, uses the proved nodup property and then obtains the root-set cardinality. Thus using a set here does not silently discard multiplicities. This particular `q` is proved separable and monic of degree six, and complex algebraic closedness yields exactly six roots.

For an **arbitrary real** matrix `B` with characteristic polynomial `q`, `exists_root_eigenbasis` first transports its actual characteristic polynomial to the complexified matrix. Each complex root is then an actual eigenvalue of the associated linear map and has a nonzero eigenvector. Injectivity of the root-subtype inclusion and the library's eigenvector independence theorem give six independent vectors. Equality with the actual complex dimension of `Fin 6 → ℂ` supplies a basis. **Diagonalizability is derived from the proved property of this concrete `q`, never inserted as a premise.** The canonical target and public trace theorem therefore retain every eligible real matrix.

`root_product_and_trace` uses that actual basis to identify the basis matrix of every natural power with the diagonal matrix of root powers. Characteristic-polynomial invariance gives the complete product of all six factors. Matrix-map/power transport, actual linear-map trace, and trace in an arbitrary basis give

\[
 \bigl(\operatorname{tr}(B^k):\mathbb C\bigr)
 =\sum_{r\in\operatorname{rootSet}(q,\mathbb C)} r^k
 \qquad(k\in\mathbb N).
\]

These are actual powers and traces of the original `B`. The argument does not assume Hermitian structure, a real spectrum or a selected companion form. All representation changes were inspected in the fresh proof terms; the short `change` steps expose the explicitly named local matrix/linear-map/coercion representations described in the module comments and proof map.

`Newton.lean` separately proves a reusable finite-family theorem for **any** indexed family of six complex numbers whose full characteristic-factor product equals `q`. Vieta's multiset formula and the evaluated multivariate Newton identity retain one term per index; no injectivity or distinctness assumption appears in this helper. The elementary symmetric coefficients, including their signs, are obtained from the actual full product equality. The seventh elementary symmetric value is zero because a six-element index set has no seven-element subset. The seven finite recurrences yield precisely the frozen table. The final trace theorem composes this result with the actual matrix trace bridge and uses injectivity of `ℝ → ℂ` to return to real equality.

This resolves the original multiplicity, field, actual trace-power and arbitrary-matrix concerns. The new definitions `elementaryMoments` and `powerMoments` contain ordinary symmetric-polynomial evaluation and finite sums; they contain no assumed conclusions. They have material consumers in the completed proof.

## Witness, exact values and the consumed LeanCert certificate

The source matrix is unchanged: `diag(1/2,C₂,C₄)`. `Witness.lean` reindexes it as a three-plus-four block matrix and proves equality with that block matrix entrywise. Actual block characteristic-polynomial identities reduce the calculation to determinants of orders three and four. It then proves

\[
 p=(X-\tfrac12)(X^2-1)(X^4-1),\qquad
 q=\frac{p'}7=X^6-\frac37X^5-\frac57X^4+\frac27X^3-\frac37X^2+\frac17X+\frac17.
\]

The monicity and exact degree are proved separately. My independent sparse determinant expansion, differentiation and direct parsing of the frozen Lean coefficients agree. Independent Newton arithmetic and actual companion-matrix powers both give

\[
 (s_1,\ldots,s_7)=
 \left(\frac37,\frac{79}{49},\frac{48}{343},\frac{6731}{2401},
 \frac{5213}{16807},\frac{219766}{117649},-\frac{8593}{823543}\right).
\]

The companion's characteristic determinant is also independently verified; it provides a nonvacuity diagnostic for the unrestricted characteristic-polynomial premise, not a universal proof. The generic theorem uses `Matrix.pow_apply_nonneg` and sums diagonal entries, including empty dimension and power zero. My fresh inspector exercises both edge cases separately.

The actual retained `numerical_negative_moment` proof calls
`LeanCert.Validity.verify_strict_upper_bound_dyadic_checked` on the expression
`(-8593) * (1/823543)`, over the singleton interval `[0,0]`, with upper bound zero, precision `-53` and depth `10`. There is no subdivision, approximate eigenvalue or root calculation. I inspected the pinned checked-validity theorem: the Boolean certificate establishes both its evaluation domain and strict bound, and its theorem conclusion is the real inequality.

The fresh proof retains the generated helper
`NLA.IS03.numerical_negative_moment._proof_1_7`. Its printed body is
`of_decide_eq_true (id (Eq.refl true))` at the exact checker equality. My additional independent command prints that same helper and separately proves the identical Boolean equality with **`decide +kernel`**. Both trust checks pass. The candidate explicitly selects kernel mode; no native fallback or additional axiom appears.

This certificate is **materially consumed**: `negative_moment_proved` uses it, `counterexample_proved` combines the seventh trace equality with nonnegative trace and that strict negative value, and the full conjecture negation instantiates the original universal claim at order seven. I inspected this actual compiled chain. The certificate is neither unused decoration nor a replacement for the exact matrix and polynomial proofs.

## Actual trust audit, reuse and adapted standards

All **18 candidate internal/public** transitive axiom reports contain exactly `propext`, `Classical.choice` and `Quot.sound`. Four additional structural checks in my inspector and two additional retained-checker checks also pass. My inspection traverses both types and proof/definition bodies from all seven exports: **61 project declarations** are safe, total and individually have only permitted transitive axioms. **33 material dependencies** are explicitly required and present, including the real/complex transport, derived basis, full coefficient and power-sum identities, and checked LeanCert validity theorem. The full proof closure has no `sorryAx`, custom axiom, unsafe/partial project declaration, native compiler trust or Challenge import.

The pinned primary APIs were read directly and independently compared with their immutable Git blobs. Seventeen relevant library/core files are recorded in [primary-api-inputs.json](proof-referee-1-evidence/primary-api-inputs.json). The proof reuses Mathlib's matrix power, block determinant, eigenvector, basis, trace, Vieta and Newton machinery. The repeated coefficient/recurrence work is organized by named elementary and power moments; no unnecessary general Jordan-form or root-isolation implementation is introduced. The exact Bézout and block reductions keep computation bounded.

I applied all ten pinned Tau Ceti angles through the repository's explicit adaptation at `afb424eda89e8ac96d9eb69f6a88972055a4cd1b`. The hashes of every rubric and local protocol are retained. This is not an official Tau Ceti service result or roadmap admission.

| Angle | Final assessment |
| --- | --- |
| Correctness and scope | PASS: full original target, exact field/order/quantifiers and all genuine semantic bridges. |
| Proof quality and reuse | PASS: exact bounded reductions, derived spectral property, reusable genuine Newton/Vieta helpers and existing Mathlib APIs. |
| Generality and API design | PASS: all natural powers and arbitrary eligible real matrices; every introduced definition has an actual consumer. |
| Naming and placement | PASS: bounded `NLA.IS03` modules separate algebra, spectral transport, witness, scalar certificate and exact exported contracts. |
| Documentation | Mathematical proof map and completion evidence are accurate; the historical statement-stage README needs the ordinary later packaging refresh below. |
| Attribution | PASS: Colbrook's mathematics, original conjecture/source credit, George's formalization and AI assistance remain distinct. |

**Packaging-only D1:** the current frozen README still says “statement-only package” and “there is no `Proof.lean` or `Solution.lean` implementation.” Preserve its reviewed historical bytes and archive them before refreshing the live candidate README to the completed-proof phase. `NUMERICAL_TARGETS.md`, `SourceCorrespondence.md` and earlier evidence should remain historical. This is not a mathematical correction and does not warrant changing any frozen proof or boundary. The eventual manifest must describe actual Linux as pending until that project-specific run and audit occur.

Matthew J. Colbrook retains mathematical authorship. George Stepaniants receives AI-assisted formalization credit with the **Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA**, without an email address. Original source attribution and licenses are not reassigned. No human peer review, new priority claim or source-author endorsement is asserted.

The exact independent commands, raw outputs, certificate, arithmetic, primary source identities, source-signature comparison, final preservation audit and offline inventory are retained in [proof-referee-1-evidence](proof-referee-1-evidence/). Its manifest binds this report as well. A second independent final referee, actual sandboxed Linux/default-kernel/Comparator success, operational acceptance and publication checks are still required before a Lean-verified promotion.
