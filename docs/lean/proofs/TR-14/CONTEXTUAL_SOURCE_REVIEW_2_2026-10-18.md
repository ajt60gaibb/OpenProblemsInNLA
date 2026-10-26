# TR-14 independent contextual product source review 2

Reviewer: OpenAI Codex AI agent `/root/fr05_statement`, 18 October 2026.
**APPROVE the nine other-author modules at the exact hashes in
[contextual-source-review-2-evidence-2026-10-18/result.json](contextual-source-review-2-evidence-2026-10-18/result.json). No source or fidelity blocker found.**
I implemented none of ProductStabilizer, UnitSpan, UnitScaleProducts,
UnitScaleAction, LinearTransformation, UnitTransformation, UnitAvoidance,
ContextualReduced or ContextualProductStep. I authored separate binary and
reduced-subalgebra modules; this review does not self-approve those proofs.

I read all nine complete actual sources and freshly compiled their unchanged
bytes into my own private object directory, using pinned Mathlib/LeanCert import
objects and the freshly built unchanged Infrastructure prerequisite. All nine
passed their LeanCert kernel assertions. Printed closures use only `propext`,
`Classical.choice`, `Quot.sound`. Source/log hashes, exact commands and raw logs
are retained in result.json. This is a local independent source replay, not a
Linux Comparator receipt or a full TR-14 proof.

ProductStabilizer is exactly the algebra of ambient multipliers preserving the
actual subspace. Its product is Mathlib's linear span of actual products.
Stabilizer multiplication equals the space, and taking further product factors
retains the action. UnitScale is the actual invertible linear multiplication
map, so its dimension equality is genuine. The intersection/sum transformation
uses a chosen actual unit and proves both product containment and the dimension
sum identity. No assumed Kneser inequality enters these definitions.

UnitSpan proves finite spectrum through the faithful multiplication operator.
A scalar translate supplies an actual unit, and one-containing spaces are
spanned by their actual units. It assumes only the displayed infinite field
and finite dimension; it does not require reducedness or finitely many ambient
subalgebras. LinearTransformation then follows the source's strict dimension
induction on the actual intersection. If the transform does not shrink, unit
spanning gives the stabilizer directly. Otherwise the strictly smaller dimension
justifies recursion and the proved dimension identity transfers the bound.
UnitTransformation correctly undoes scaling by the chosen unit; it preserves
the same auxiliary subalgebra action. This implements the commutative finite
version of the credited Beck–Lecouvey transformation argument.

UnitAvoidance supplies a mathematically valid alternative to the manuscript's
Vandermonde parameter curve. Finite proper subspaces cannot cover the actual
units in a one-containing space: first choose a point outside the subspaces,
then exclude finitely many scalar-line intersections and finite spectral bad
translates. If finitely many classes cover all units, one class must span the
space. This proves the needed common-auxiliary conclusion without a genericity
oracle or an unjustified infinite pigeonhole step.

ContextualReduced retains the exact annihilating functional and all-but-one
projection conditions. A nilpotent's component in the reduced coordinate factor
vanishes; the Frobenius pairing and actual first-factor surjectivity then kill
its other component. The source applies this to every transformation auxiliary,
using the actual stable T-space and product containment. Thus each selected
auxiliary is proved reduced before it enters the finite grouping.

ContextualProductStep groups only these proved reduced auxiliaries. Finiteness
of reduced subalgebras is an explicit premise at its general-field interface,
not a claim about all subalgebras of a nonreduced ring. One class spans U;
its actual auxiliary acts on every product by linear extension, so it lies in
the actual product stabilizer. Its existing dimension bound gives the exact
contextual one-step inequality. No symmetric or Vandermonde restriction on an
ordinary decomposition is introduced at this layer.

The arbitrary ordinary decomposition, actual graph subspaces, whole-local-factor
primitive blocks, polynomial-image dimensions and final minimum lower bound
are separate remaining applications. This report certifies these support
sources only. The separately proved complex finite-dimensional reduced-subalgebra
finiteness theorem can discharge the displayed finiteness premise in an actual
complex application; its independent approval is supplied by other agents.
Permanent IDs, original documents and frozen all-width Target remain unchanged.
