# IE-04 source correspondence and frozen proof boundary

Original solution and formalization author: George Stepaniants, Department of
Computing and Mathematical Sciences, California Institute of Technology,
Pasadena, California, USA. Historical conjecture attribution remains with
Spielman and Teng. Substantial AI assistance is disclosed; no external human
peer review or completed formal verification is asserted by this candidate.

The complete [canonical IE-04 problem](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/8f04b905eb2e0827b6b84f37d9d080ae1f05b202/linear-systems-and-elimination/IE-04/README.md)
and [solution](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/8f04b905eb2e0827b6b84f37d9d080ae1f05b202/linear-systems-and-elimination/IE-04/solution.md)
were read in full. Their immutable Git blobs and SHA-256 hashes are recorded in
`SOURCE_HASHES.json`. The final target is the nonexistence of the full pair of
uniform positive tail constants, not only a finite-dimensional growth example.

`Mat n` is the actual real n-by-n matrix space. `spectralNorm` is the induced
Euclidean operator norm through `Matrix.Norms.L2Operator`. The generic
partial-pivoting definitions are adapted from the already formalized IE-05
`Definitions.lean`, `Pivot.lean` and `GEPP.lean` at the same upstream commit.
The original generic implementation was AI-assisted work for George Stepaniants.
Source reuse does not import that problem's numerical witness or conjecture.

The scan chooses the smallest current row index attaining the largest absolute
entry in the active first column. The row swap and division-based Schur update
are explicit. Active matrices are padded with zero outside their trailing blocks,
and the actual finite growth numerator ranges over exactly stages 0 through
n−1. `entryMax_semantics` and `firstPath_semantics` expose the bridge from this
implementation to the independent mathematical maxima and admissible-path
specifications. The first-path admissible-rule theorem also proves that its
growth is Borel measurable.

`gaussianMatrix n` is the actual nested finite product of the n² probability
measures `gaussianReal 0 1`. It is not a symbolic certificate for some unknown
distribution. The Challenge requires a probability-measure theorem, a measurable
rectangle theorem with the exact product of scalar interval measures, and
measurability of the actual algorithm's tail event. Its 21 targets are listed
by exact name in `comparator.json`.

`AdmissibleRule` ranges over deterministic tie choices that are valid on every
nonsingular input and have measurable growth. In particular, it does not restrict
to the no-swap rule or assume the certificate's conclusion. `firstPath` is proved
to be a member so this class is nonempty. `full_box_robust` independently proves
strict pivots, an actual admissible no-swap path, equality of every admissible
path with it, and nonsingularity throughout the full entrywise witness box. The
probability lower bound and counterexample apply to **every** admissible rule.

The canonical problem is stated for nonsingular perturbed inputs, which are
almost surely the Gaussian case. Our tail event explicitly intersects with
`det A≠0`. This avoids using an unproved nullity fact, and is sufficient in the
strong direction needed for a negative result: this event is a subset of any
total-extension growth-tail event that agrees with GEPP on nonsingular matrices.
A uniform upper bound for the original event implies the same upper bound for
this restricted event by measure monotonicity. Thus disproving the restricted
bound disproves the original bound regardless of any convention on singular
inputs. No equality of the two probabilities or almost-sure tie claim is used
without proof. Measurable tie rules include the usual finite-comparison
implementations; the entire positive-measure box has strict pivots, so none can
avoid the lower bound there.

`UniformExponentialTail` retains every dimension n≥1, every real center with
spectral norm ≤1, every noise scale 0<σ≤1, every real threshold x≥1, and arbitrary
real positive c₁,c₂. The displayed negative witness uses the allowed center Iₙ
with actual spectral norm one and σ=1, as in the source. The last Challenge
declaration negates the complete proposition. There is no assumption that the
large-growth box center Wₙ itself has spectral norm ≤1.

The source's formulas use one-based stage numbers; this package uses stage
`k=0,...,n−1`, with final-column values `(3/2)^k`. Consequently the final growth
threshold is `(3/2)^(n−1)/2`, exactly the source's. The proof obligations preserve
its radius `1/2^(n²+n+1)`, amplification `2^(n+2)` and probability lower bound
`1/2^(n²(n²+n+5))`. The arbitrary-real-exponent asymptotic theorem is explicit and
does not just test finitely many proposed constants or dimensions.

The scalar quotient and Schur-update estimates, induction over stages, and
finite-product Gaussian rectangle reduce the computational burden without
reducing the mathematical target. A fixed one-dimensional density bound and
rational constants suffice. No matrix-valued interval subdivision, Monte Carlo
probability claim, sampled perturbation box or external numerical certificate
is used as a theorem premise.

The source's additional center-zero result, the weaker shorthand `2^(−3n⁴)`,
and the supplementary finite interval-check script are not required by the
canonical negative conclusion and are not separate verification claims here.
No alternative optimal tail, expectation estimate, or bit-level arithmetic
statement is claimed.

All 21 frozen obligations passed the complete actual non-root Linux development
build in run 35031607095 at commit 4bd2d76ec6e37696ff0c2d5feacf21e342371f27.
The current standalone mathematical files are byte-identical to those accepted
inputs. Each Solution export passed its LeanCert kernel assertion and printed
only propext, Classical.choice and Quot.sound. The aggregate shared run failed
in the separate MF-12 project; the complete original receipt is retained.
The Definitions and independent Challenge had already passed Linux elaboration
after two independent statement approvals; STATEMENT-FREEZE.json is unchanged.

Two complete mathematical source reports and the current independent
source/development addendum are retained under reviews/. The root report names
its earlier snapshot; final reconciliation by both referees remains pending.
The historical candidate documentation is preserved under
verification/packaging/before/. Preparing metadata and the standalone Lake
target is a packaging contribution distinct from independent proof review.

Complete development compilation is not final canonical verification. Actual
canonical Comparator and independent default-kernel replay with rejection
controls, plus two final source/evidence addenda, remain necessary before
publication acceptance or a verified count. Adapted Tau Ceti review angles are
mathematical scope, correctness, useful source reuse and clarity; this is not
an official Tau Ceti certification-service claim. Optional source corollaries
remain outside the claimed scope and do not replace the canonical negation.
