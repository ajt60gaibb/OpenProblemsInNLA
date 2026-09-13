# PR 193 independent IV-06 source and mathematical audit

**PASS for the complete original negative answer.** Reviewed head
`f73edd6c6562a78d1c4f56fdc4c1c75dac9ace4a`, comparison base
`5830ed4fb06da0659414a3deb2a40ad327aca052`, 12 September 2026.
Reviewer: coordinating Codex AI agent. This is independent AI auditing, not
external human peer review or a claimed local Lean execution.

I read all of Definitions, Proof, Challenge and Solution, the comparator
configuration, and the original canonical statement. The full quantifiers are
preserved: every positive dimension and every real independent-entry closed
box with ordered endpoints. Singleton entries are allowed. A real eigenvalue
requires an actual nonzero real eigenvector. Components are those of the
attained subset with its real subspace topology, and their number is the actual
Cardinal of ConnectedComponents. Infinite component spaces cannot disappear
through a finite-cardinality default. No symmetry, genericity, diagonalizability
or all-real-spectrum hypothesis is inserted.

The primary 2011 question is the at-most-dimension bound for the full
independent-entry family, as recorded in
[Hladik–Daney–Tsigaridas](https://doi.org/10.1016/j.cam.2010.11.022), section 1,
printed page 2716. I checked the original statement through its indexed paper
text and author publication record. The canonical target is unchanged.

## Complete proof

1. Determinant zero is proved equivalent to a genuine nonzero null vector of
   lambda I-A, then to the original eigenvector equation. This also behaves
   correctly at dimension zero, although the conjecture excludes that case.
2. Entrywise lower and upper bounds force all seven fixed entries to their
   common values; the remaining two entries vary independently over the exact
   intervals [-166,-16] and [9,159]. Both directions of this family equality
   are proved, so no smaller selected subfamily replaces the target box.
3. The actual determinant is expanded for all real a,b,lambda. I independently
   reconstructed it as lambda^3-25lambda^2-lambda+25-a lambda+a-b lambda-b.
4. All four supplied integer matrix-vector equations and nonzero vectors were
   independently checked exactly, at eigenvalues -3,0,3,25. Each parameter
   pair belongs to the full box.
5. At separators -1,1,12 the determinant is affine in a,b. Independent exact
   corner calculations prove its full ranges are [-332,-32], [-318,-18] and
   [-3750,-150]. Thus no matrix in the box attains any separator. The Lean
   proof proves the bounds universally by linear arithmetic. Its explicit
   kernel LeanCert fact -18<0 is consumed by all three strict exclusions; no
   numerical eigenvalue or root-isolation claim is made.
6. Equality of two actual component classes implies they lie in one connected
   component of the subtype. Its continuous inclusion in the real line has
   preconnected image, which contains every intervening point. I inspected
   the pinned Mathlib ConnectedComponents quotient and coe_eq_coe' at
   `0df444a360eaa60ab8c11dca51a86af692955474`, lines 503–530, through the
   [official source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Connected/Clopen.lean).
   No closedness or finite-component assumption is needed for this argument.
7. A separator lies between every distinct ordered pair of the four included
   values. Interval containment would contradict its exclusion. This proves
   an actual injection Fin 4 into the component quotient, hence cardinality
   at least four. The universal dimension-three bound would then contradict
   3<4. The complete original proposition is negated.

## Trust and scope

All eight actual Solution signatures match the separate Challenge boundary.
Only Challenge contains intentional placeholders; Solution imports Proof,
which imports Definitions and pinned library/tactic modules. No definition
exceptions, unproved hypotheses or added axioms occur in the actual proof.
The comparator permits only propext, Classical.choice and Quot.sound.

The independently downloaded current upstream Linux run
[34727780424](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/34727780424)
succeeded on the exact reviewed head. Its checked merge parents are the
published base and that head. All 596 recorded inputs match the complete
tracked project, its configuration and source lock match, eight exports are
accepted with actual default-kernel replay, and all 17 axiom reports contain
only the standard three axioms. The actual kernel/Comparator/sandbox controls
and admitted/native-proof rejection controls passed. This is authenticated
execution evidence, distinct from the mathematical-fidelity review.

The conclusion is at least four components, not exactly four or a formula for
all endpoints. The page states those limits accurately and retains Colbrook's
counterexample authorship and Stepaniants's formalization credit. A separate
reviewer independently checked the proof bridges and all three canonical PDF
pages. Exact reconstruction results are retained in
`/private/tmp/nla-pr193-independent-exact.json`.
