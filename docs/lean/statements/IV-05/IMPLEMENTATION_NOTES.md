# IV-05 implementation correspondence

Implementation and specification author: OpenAI Codex AI agent
/root/statement_design, 2026-09-28. Independent specification approvals from
/root and /root/inventory were verified against final hash
a70e3008bfa3cfae8b068fc3af690a761ee44f75bb46a2fb2a8d101ede2ff931.
The ordinary computation model already had independent final reviews.
No interval-hull solver or proof of its polynomial complexity is implemented.

OrderedInput keeps the original weak rational endpoint inequalities.
InMatrixInterval and InRhsInterval range over all independently varying real
entries between the exact rational-to-real embeddings. InputPromise requires
positive dimension, endpoint order and the inverse-M condition for every matrix
in that entire interval.

NonsingularMMatrix is precisely an invertible real matrix with nonpositive
off-diagonal entries and entrywise nonnegative inverse. InverseMMatrix guards
A.det!=0 and applies that full definition to A inverse. Both determinant guards
make every imported total matrix inverse a genuine inverse. This directly
states the source definition instead of relying on an unproved equivalence or
silently adding positive diagonals, strict signs or irreducibility.

IsSolution uses existence of A,b in their independent intervals and the exact
ordinary equations A*x=b. Under the input promise A is invertible, so this is
exactly the original x=A inverse b solution set. ExactHull gives for each
coordinate a universal enclosure and separate lower and upper attainment
witnesses in that full solution set. The witnesses may differ across endpoints
and coordinates. No simultaneous extremizer or independently enclosed inverse
is substituted.

Target first chooses one actual finite binary transducer and one fixed
PolynomialBound, then every promised input. The rational lower and upper output
vectors have exactly that input dimension. encodeIntervalOutput emits the
dimension followed by all lower and all upper endpoints in the fixed normalized
binary rational grammar. RunsWithin requires those actual output bits on a
terminal tape after at most coefficient*(inputLength+1)^exponent transitions.
No endpoint bit length, output-writing cost or dimension is ignored.

There is no requirement on behavior outside InputPromise, including malformed
or off-promise inputs. Promise recognition, an exact LP oracle, real arithmetic
at unit cost or an arbitrary evaluator is not part of the ordinary machine.
The fixed imported definitions were independently reviewed; no general codec
inversion or simulation theorem is assumed. Proving the known 2n-LP solver and
its rational bit complexity is separate future work.

All degenerate widths, n=1, zero or mixed-sign right-hand sides, zero solution
coordinates, reducible inverse-M matrices and zero off-diagonal inverse entries
remain in the source domain. Exact rational output, uniform binary polynomial
time and each endpoint's attainment all remain mandatory.

The closed Target definition explicitly selects LeanCert kernel trust and runs
#assert_statement, #assert_trust kernel and #print axioms. Pinned local Lean
4.33.1 compilation passed with only propext, Classical.choice and Quot.sound.
Author-local evidence is in /private/tmp/nla-av01-iv05-evidence; builds are in
/private/tmp/nla-av01-iv05-build. Final independent reviews must inspect the
source and frozen boundary with the full computation/encoding import closure
and pins. No target proof, status promotion or Linux Comparator pass is claimed.
