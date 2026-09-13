# MF-16 complete proof correspondence

This is an implementation-author map, not an independent final review. George
Stepaniants receives AI-assisted formalization credit with Department of
Computing and Mathematical Sciences, California Institute of Technology,
Pasadena, California, USA. Matthew J. Colbrook retains mathematical authorship
of the counterexample; Hillar–Johnson and Armstrong–Hillar retain source credit.
The main implementation author is `/root/leancert_examples` and the genuine
Cayley–Hamilton helper author is `/root/solved_statement_inventory`. Root made
a disclosed computation-route contribution. None of these roles qualifies as
an independent final mathematical referee of this implementation.

`Definitions.lean`, the numerical plan, `Challenge.lean`, source correspondence,
Comparator configuration and all dependency pins are unchanged from the two
approved statement reviews. The complete all-word, all-complex-Hermitian-PD
order-two uniqueness target is retained. The final theorem refutes that target;
it does not classify every solution or prove the manuscript's stronger
three-solution and exponent-threshold claims.

| Frozen export | Actual proof route |
| --- | --- |
| `word_semantics` | `Algebra.witness_eval` proves the actual `List.prod` equals the written matrix product using the genuine natural power. The palindrome and 16-letter/14-X/2-B counts are kernel reductions. |
| `source_data` | The original B, P and X0 are unchanged. An invertible LDL congruence proves genuine complex positive definiteness. Actual diagonal matrix powers and multiplication prove the source equation; true determinants are computed exactly. |
| `twelfth_power_reduction` | `CayleyHamilton` proves an exact scalar polynomial remainder identity, then applies Mathlib's `Matrix.aeval_self_charpoly` and genuine 2×2 characteristic polynomial. Its generic result applies to every real 2×2 matrix of determinant three, with no symmetry or diagonalizability assumption. |
| `polynomial_word_equivalence` | `Polynomial` proves the actual Expr evaluations equal det(S)−3 and the first two reduced matrix residuals. The first equation supplies the determinant-three premise. `Proof.reducedWord_eq` then uses the true matrix-power theorem, proving the unconditional two-way equivalence with the original word. |
| `krawczyk_certificate` | `Numerical` proves the complete actual Boolean by `decide +kernel`, plus the exact preconditioner determinant, radius and strict whole-box contraction bound. All certificate inputs are the frozen rational data. |
| `certified_root` | The retained Boolean is supplied to the actual `LeanCert.Engine.krawczykCheck_sound`. This gives an actual real root, unique in the closed box; it is not an assumption or a residual test. |
| `root_to_matrix` | The box forces the first coordinate above three. Positive first minor and determinant three imply complex Hermitian PD by the generic LDL lemma. Actual transpose and determinant multiplicativity recover the unchecked lower diagonal entry from the two known entries. Matrix ring-homomorphism identities transport the full product into complex matrices, and the first entry distinguishes the root from X0. |
| `counterexample` | The certified root yields a second distinct complex PD solution alongside the unchanged source solution, for the actual palindrome and fixed PD B,P. |
| `not_wordUniquenessConjecture` | Applying the full original all-word/all-complex-data uniqueness statement to the two actual solutions contradicts uniqueness. No degree theorem is assumed. |

## Numerical work minimized and materially consumed

There is one box in three independent real coordinates, with rational radius
`1/10000000`, and one frozen rational preconditioner. The interval computation
uses only const/var/add/mul/neg Expr constructors. It checks det(S)−3 together
with the two Cayley–Hamilton-reduced word entries. No reciprocal occurs in the
AST, no denominator equation is discarded, and no numerical eigenvalues or
high matrix powers are interval-expanded. The nonzero preconditioner
determinant and the actual whole-box bound `<27/1000` are proved in the kernel.

The actual retained Boolean proof is
`NLA.MF16.actual_krawczyk_checked._proof_1_1`. It feeds
`actual_krawczyk_checked`, then `krawczykCheck_sound`,
`certified_root_proved`, the matrix-recovery theorem and the full original
negation. The LeanCert theorem derives AD support/differentiability, a genuine
Jacobian enclosure, the actual operator norm bound, closed complete box and
strict contraction/self-map, Banach fixed-point existence and invertible-
preconditioner fixed-point/zero equivalence. None is an unproved project premise.

Local uniqueness in the additional root's box does not assert uniqueness of
the original matrix equation: X0 is outside the box. One additional real
symmetric solution, proved complex PD after the real embedding, suffices for
the full complex counterexample.

## Validation boundaries

Every proof module has compiled without a hole or native execution trust.
`Solution` supplies exactly the nine frozen signatures and does not import
Challenge. The separate admitted Challenge module only defines the reviewed
comparison targets. The source/default Lake target remains Challenge, with
the Solution library already registered; explicitly use `lake build Solution`
on a normal checkout with its own dependencies.

The final author check freshly elaborates eight implementation/definition
modules, a separate actual dependency inspector and Challenge into an empty
private project prefix. It uses the ten clean pinned MI-22 dependency sources
and objects read-only, excludes every old MF-16 project object, and performs no
Lake build, dependency copy or download. Actual command receipts, source
snapshots, logs and hashes are retained in `verification/final/`.

The inspector follows types and bodies from all nine exports, checks every
reached project declaration for unsafe/partial status and forbidden axioms,
and separately follows nine material LeanCert soundness steps. The exact
counts and identities appear in its actual log and `source-audit.json`.
This is an author check, not a third-party proof review or Linux success.
Two independent final mathematical reviews, truthful v0.4 completion metadata,
actual Ubuntu Comparator/default-kernel/negative-control verification and
operational/publication review remain separate gates. The canonical status
is still Solved. Earlier statement-stage pending notices remain historical;
their exact bytes are intentionally preserved until candidate packaging.
