# AA-01 implementation correspondence

Specification and implementation author: OpenAI Codex AI agent
`/root/inventory`, 2026-09-28. Before writing Lean I verified the independent
`/root` and `/root/statement_design` approvals against all bound inputs.
The approved specification is SHA-256
`ae12a6116c32ee45e2125512dc44d28783d6158e592853a98caa9d9806ff741d`.
The complete canonical README remains byte-identical to ORIGINAL.md. No
canonical source, old Lean proof, already reviewed machine/codec module,
package pin, metadata record or generated aggregate module was changed.

The shared RoundedTree helper contains a genuine finite inductive syntax.
Program r can return an available register, append exact unary negation,
append one rounded addition/subtraction/multiplication, or compare two actual
registers and choose one of three finite continuations. The syntax contains
no numerical constants, real-function fields, oracle or loop. Fin.snoc keeps
all existing register values and appends one result. Reading a stored result
again therefore reuses its earlier error; reexecuting an operation at a
separate syntactic node uses a new independent error. Exact comparisons do
not produce numerical registers and are allowed to branch on rounded values.

roundedCount counts every rounded node across all branches. Evaluation uses
one Fin roundedCount error vector. A rounded node reads coordinate zero and
passes the successor-coordinate tail to its continuation. A comparison uses
three disjoint contiguous blocks in less/equal/greater order, with offsets
zero, less.roundedCount and less.roundedCount+equal.roundedCount. These offsets
are determined by the complete syntax, even when a branch is not executed.
Each block has statically proved in-range indices; no default errors or
dynamic renumbering are used. Arithmetic is the actual real operation times
(1+delta) and negation is exact. Structural recursion terminates on every
input and error vector. Classical real comparisons explain noncomputable
Lean evaluation; they are exactly the specified arithmetic model, not an
oracle supplied to the separate binary decision machine.

PolynomialInput has a natural dimension and a finite list of signed integer
coefficient/exponent-vector monomials. PolynomialValue sums every occurrence
using genuine finite real products and natural powers. Duplicate monomials,
zero coefficients and cancellation remain valid syntax. ValidInput checks
the collected exact constant value p(0)=0, rather than incorrectly requiring
each constant occurrence to vanish. encodePolynomial explicitly emits the
dimension and list length, then each signed coefficient followed by all
natural exponents in coordinate order. It uses the reviewed BinaryEncoding
without changes. Integer coefficients belong to the decision problem's
encoded polynomial, not to the constant-free evaluator's initial registers.

Accurate requires zero-error correctness on every real input and then
forall eta in (0,1), exists u in (0,1), forall real inputs x and independent
error vectors bounded coordinatewise by u, the exact relative inequality
|computed-p(x)| <= eta*|p(x)|. The same finite Program is fixed before eta,
and u is uniform in x and all errors, including unused-branch coordinates.
At every zero of p, the computed value must be exactly zero. There is no
absolute floor, exceptional set, generic-input assumption or probabilistic
rounding interpretation.

The explicit zero-variable boundary follows the approved source convention:
Program 0 is empty because every initial constructor requires an available
register. Thus the zero-variable zero polynomial is a valid negative instance
of AccuratelyEvaluable. This convention is disclosed in the specification;
it does not silently restrict n>=1 or introduce a numerical zero literal.
For positive dimension, subtracting an input from itself yields exact zero
under every rounding error and satisfies the full uniform accuracy predicate.

AA01.Target is the original decision question. It chooses one ordinary
FiniteMachine before every valid encoded polynomial, then requires an actual
finite halting time and a Boolean answer equivalent to AccuratelyEvaluable.
DecidesWithin invokes actual binary tape execution and the exact one-bit
output convention. Its time witness may depend on the input: no polynomial
bound is imposed, and there is no assumed quantifier-elimination algorithm,
LP solver, supplied evaluator-existence predicate or oracle. Behavior outside
the valid encoded input domain is unrestricted. General codec inverse and
conventional-machine-equivalence proofs remain separate future work and are
not assumed axioms. No target theorem is asserted.

RoundedTreeControls gives symbolic kernel proofs that a stored rounded sum
is reused twice, two separately executed sums have distinct errors, negation
is exact, rounding can change comparison outcomes, all three branches are
counted, and unequal-size branch blocks use the expected static coordinates.
A greater-branch result ignores all unused earlier branch errors. The full
polynomial encoding order is checked without expanding long bitstrings.
Further controls prove full accuracy of the positive-dimensional zero
polynomial, impossibility of a zero-variable tree, and exact cancellation of
integer constant terms. No native_decide, numerical sampling or relaxed
heartbeat/recursion limit is used.

The helper owns the shared syntax and evaluator, so live and frozen Target
copies import the identical definitions. The frozen file is the standard
header plus exact namespace substitution. The author-local fresh pinned
Lean 4.33.1 build includes every local dependency, helper, controls, live and
frozen modules, followed by an actual rfl equality theorem and LeanCert kernel
trust assertions. Distinct logs and source hashes are retained in
/private/tmp/nla-aa01-evidence/results.json, with final reviewed inputs in
final-inputs.json. Both Target definitions and their equality report only
propext, Classical.choice and Quot.sound. This is author-local macOS kernel
elaboration and definitional equality, not a proof of decidability and not a
Linux Comparator or CI result. Independent final reviews must bind the full
local import closure, frozen source, all three pins, specification, complete
original, these notes and semantic controls.
