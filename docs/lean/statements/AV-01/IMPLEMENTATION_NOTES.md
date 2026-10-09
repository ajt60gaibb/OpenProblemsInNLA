# AV-01 implementation correspondence

Implementation and specification author: OpenAI Codex AI agent
/root/statement_design, 2026-09-28. Independent specification approvals from
/root and /root/inventory were verified against final hash
d524be200a4238cc2b23c86eb08523bb76fe4c6accc5dac204451f2cc335b3cf.
The ordinary computation model had final independent reviews by /root and
/root/statement_design before this target was written. This file defines a
machine-existence proposition and does not construct or prove a solver.

IsSolution uses every real vector of the input dimension, exact rational-to-real
casts, the full matrix row sum and the componentwise real absolute value.
HasExactSolutionCount is Nonempty of an equivalence from Fin(2^n) to the entire
solution subtype. It asserts exactly the finite number of distinct real points;
infinite solution sets cannot satisfy it. No sign, regularity, nonsingularity,
genericity or finite-cardinality input promise is added.

Target chooses one actual FiniteMachine and one PolynomialBound before every
AVInput of positive dimension. It asks for one Boolean whose exact one-bit
output is produced by that machine in coefficient*(encodedLength+1)^exponent
transitions, and whose equality to true is equivalent to HasExactSolutionCount.
The coefficient is a positive natural and the exponent is a natural. All
dimension and normalized rational coefficient bits are part of encodeAV.
Constants and the machine cannot depend on the input.

The imported fixed alphabet, finite transition table, TM0.step, bounded trace,
terminality and exact output convention were reviewed in the shared ordinary
model. This is binary bit complexity, not unit-cost rational arithmetic.
The explicit encoder covers every rational A,b in dense row-major form.
The target operates on these exact encoded mathematical inputs and requires
nothing of malformed words; no analytic promise recognizer or LP oracle enters
the statement. General codec inversion/model-translation theorems remain
separate from the concrete definition and no such unproved theorem is assumed.

The full canonical classification question is answered by the affirmative
membership-in-P proposition, as specified and independently reviewed. It is not
replaced by the LP characterization or by a target theorem. The original
canonical page and proof credit remain unchanged.

The module explicitly selects LeanCert kernel trust and runs #assert_statement,
#assert_trust kernel and #print axioms. Pinned Lean 4.33.1 local macOS compilation
passed with only propext, Classical.choice and Quot.sound. Author-local build and
log evidence is at /private/tmp/nla-av01-iv05-build and
/private/tmp/nla-av01-iv05-evidence. Final independent reviews must bind the
shared computation/encoding import closure, source, frozen copy and pins.
Neither elaboration nor identity proves the catalog target, and no Linux CI or
Comparator run is claimed by this author note.
