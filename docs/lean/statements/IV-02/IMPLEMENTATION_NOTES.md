# IV-02 implementation correspondence

Specification and implementation author: OpenAI Codex AI agent
`/root/inventory`, 2026-09-28. Before implementation I verified both independent
`/root` and `/root/infra_audit` specification approvals against every bound
input. Approved specification SHA-256: `19234a7806b52868f56723f6e6bad413d174d6ad1ac56f88b3b4bcb2ea36c922`.
No existing canonical file, old Lean file, reviewed machine/codec source,
dependency pin, metadata record or generated identity file was modified.

IV02.Target covers every ordered BandInput with n>=2, including singular
members, zero widths and zero crossings. CorrectRange requires universal
lower and upper determinant bounds over every real MatrixMember together
with a separately attaining matrix for each rational endpoint. This is the
exact determinant minimum and maximum, with no shared-extremizer premise.
The output is encodeRat dlo followed immediately by encodeRat dhi, retaining
both exact rational numbers in the approved order. Compactness and
multiaffinity explain the mathematical semantics but are not assumed proofs
or replacements for the uniformly bounded machine.

This repairs the old arbitrary Prop-valued ComplexityContract and its missing
computation semantics. No historical reduction identity is erased or treated
as a complete proof of hardness or an algorithm.

The shared NLA.Computation.BandIntervals helper is authored by the same AI
agent. It imports the already reviewed FiniteMachine and BinaryEncoding
without modifying either. RationalInterval syntax stores two rational fields;
Ordered is a separate lower<=upper condition. BandInput stores exactly n
such intervals on the diagonal and n-1 on each adjacent band. edgeLeft and
edgeRight are the bounded indices i and i+1. MatrixMember applies the upper
interval to (i,i+1), the lower to (i+1,i), and forces all other off-band
positions to zero. Every matrix entry is a real value independently satisfying
its own interval, even when intervals coincide. Dimension restrictions are in
the individual Target, not silently added to the helper.

encodeBand contains one encoded dimension, followed by lower/upper endpoint
pairs in increasing diagonal, upper-band and lower-band order. encodeSystem
appends RHS endpoint pairs in coordinate order without another dimension.
All values use the previously reviewed canonical rational encoder. The helper
supplies explicit encoders; no arbitrary map, presumed polynomial evaluator,
unit-cost arithmetic or decision oracle enters any statement. General inverse
codec and conventional-machine-equivalence proofs remain separate future
proof work, not axioms or premises. Only the mathematically valid encoded
input domain is required; malformed-word behavior is unrestricted.

One actual FiniteMachine and one PolynomialBound precede all input dimensions
and endpoint data. RunsWithin demands a reached terminal machine configuration
and the exact complete output tape suffix within C*(encodedLength+1)^k actual
binary transitions, where C is a positive natural and k is natural. The output
is existentially specified only after this same uniformly bounded machine has
been fixed. Consequently these targets do not collapse into pointwise
existence of mathematical extrema or an arbitrary set-theoretic selection.

The new helper owns the endpoint inductive types and exact shared semantics,
so both target copies import identical definitions. Each frozen target is the
standard immutable header plus exact namespace substitution; actual rfl
identity was compiled for both targets. Only the original affirmative
algorithm-existence question is called Target. No target theorem, P=NP
assumption, unconditional negative answer, or conjunction with the separate
credited complexity classification is introduced. The canonical pages and
historical incomplete Lean work remain unchanged.

BandIntervalControls checks the full compact order with distinct stamped
rational endpoint fields, RHS layout and mixed finite/infinite output tags.
It distinguishes an empty output from a zero box. Actual singular consistent
and inconsistent one-dimensional systems satisfy the full-real-hull and
global-empty predicates respectively. An explicitly disconnected projection
set also satisfies the genuine negative/positive infinity clauses while
excluding zero; this tests the endpoint semantics, not a new proof of that
set's interval-system representation. Structural kernel proofs of syntax
identities avoid expanding long bit lists; no native_decide or relaxed
heartbeat/recursion limits are used.

All source modules, controls, live and frozen targets were freshly compiled
with pinned Lean 4.33.1 into /private/tmp/nla-iv02-iv04-build. The complete
source-hashed author-local receipt and distinct logs are in
/private/tmp/nla-iv02-iv04-evidence/results.json. Both Target definitions and
both actual equality theorems report only propext, Classical.choice and
Quot.sound. Target modules explicitly select LeanCert kernel trust and run
#assert_statement, #assert_trust kernel and #print axioms. These checks do not
prove a polynomial algorithm, the P=NP equivalences, or any catalog resolution.
No Linux Comparator or CI result is claimed. Final independent reviewers must
bind the entire live/frozen local import closure, three package pins, the
approved specification, complete original and these notes.
