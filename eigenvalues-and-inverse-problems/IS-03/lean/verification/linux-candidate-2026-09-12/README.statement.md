# IS-03 Lean statements awaiting independent review

This package specifies the complete negative answer to [IS-03](../README.md),
Johnson's derivative-realizability conjecture. **It is a statement-only
package.** The seven `Challenge.lean` declarations deliberately contain
`sorry`; there is no `Proof.lean` or `Solution.lean` implementation. Successful
typechecking does not prove these declarations. The canonical entry remains
**Solved** on its existing informal evidence.

The statement authors are the campaign's root and statement-inventory agents.
Two different agents must approve the frozen mathematical boundary before any
implementation begins. Two independent final proof reviews and an actual
successful Linux Comparator/default-kernel run with the required controls will
also be needed before any later status promotion.

Formalization credit: **George Stepaniants, Department of Computing and
Mathematical Sciences, California Institute of Technology, Pasadena,
California, USA**, with AI-agent assistance. **Matthew J. Colbrook** retains
mathematical authorship of the counterexample. Johnson and
Hoover–McCormick–Paparella–Thrall retain the original conjecture and source
attribution. The new formalization code uses the included Apache 2.0 license;
this does not relicense or reassign the source manuscript.

## Exact scope

`DerivativeRealizabilityConjecture` quantifies over every natural `n ≥ 5` and
every real entrywise-nonnegative `n × n` matrix `A`. It asks for a real
entrywise-nonnegative matrix of exactly order `n - 1` whose **actual** Mathlib
characteristic polynomial is the **actual** formal derivative of `A.charpoly`
scaled by the real reciprocal of `n`. Equality is equality of real
polynomials. No diagonalizability, symmetry, irreducibility, invertibility,
simple-spectrum or zero-trace premise is present.

The unchanged source witness is `diag(1/2, C₂, C₄)`, of order seven. Its actual
characteristic polynomial, derivative, and all seven trace moments of **every**
real potential order-six realization remain proof obligations. In particular,
the negative seventh trace is not inserted as a hypothesis. A complete proof
will refute the full universal conjecture at this admissible witness. The
source's stronger claims about arbitrary zero padding and a separate moment
conjecture are outside this package's exports.

| Declaration in `NLA.IS03` | Contract |
| --- | --- |
| `nonnegative_power_trace` | Every natural power of every entrywise-nonnegative real matrix has nonnegative entries and trace, including dimension and power zero. |
| `witness_admissible` | The actual order-seven source matrix is entrywise nonnegative and has trace `1/2`. |
| `witness_polynomials` | Its genuine characteristic polynomial and normalized derivative equal the displayed polynomials; the derivative is monic of degree six. |
| `trace_moment_certificate` | Every real order-six matrix with that characteristic polynomial has the seven stated power traces, without additional spectral assumptions. |
| `negative_moment` | The seventh value is exactly `-8593/823543` and is negative. |
| `counterexample` | No entrywise-nonnegative order-six matrix realizes the actual normalized derivative of the admissible source matrix. |
| `not_derivativeRealizabilityConjecture` | Negation of the complete original all-order conjecture. |

The numerical plan was written before the Lean declarations in
[NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md). See
[SourceCorrespondence.md](SourceCorrespondence.md) for source locations,
definition semantics and remaining proof obligations. The source manifest
binds the retained original documents to upstream commit
`f41f1f9ffa2171550d4bb795862c6170c4f26070`.

## Local statement checks and pins

Pinned Lean is `leanprover/lean4:v4.33.1`. The dependency manifest fixes
LeanCert at `621a43d7cf21f87872392a01e874f2f1dbddc926` and Mathlib at
`0df444a360eaa60ab8c11dca51a86af692955474`, together with the eight transitive
packages. `lakefile.toml` selects `Challenge` by default and already registers
the future `Solution` library. `comparator.json` lists exactly the seven
contracts, no definition exceptions, and only `propext`, `Classical.choice`
and `Quot.sound` as permitted axioms.

The author ran three fresh macOS source commands: Definitions, Challenge and
an inspection module. All returned zero. Definitions and inspection produced
no warnings; Challenge produced only its seven intended `sorry` warnings.
Actual elaboration confirms the matrix semiring power instance, the sum of
diagonal entries for trace, determinant of the characteristic matrix, real
polynomial derivative/scalar action, and the exact quantifiers. Three
definition-only LeanCert kernel trust checks passed; they do **not** establish
the admitted theorem targets or execute the planned scalar certificate.

These runs used a new empty project output prefix and reused the ten clean,
pinned MI-22 dependency caches **read-only**. They did not copy dependencies,
rebuild Lake dependencies, import old IS-03 objects or run Linux Comparator.
The absolute cache paths, complete `LEAN_PATH`, commands, source hashes,
timestamps, exit codes and raw outputs are in
[reviews/statement-evidence](reviews/statement-evidence/).

On this workspace, the retained author checks can be reproduced with:

```
python3 reviews/statement-evidence/reconstruct_exact.py
python3 reviews/statement-evidence/run_statements.py
```

The exact diagnostic parses the actual Lean literals, expands only supported
determinant terms, differentiates the polynomial, reconstructs all seven
moments by Newton's recurrence and independently computes companion-matrix
traces. It passes without root approximation or floating-point arithmetic.
The companion calculation checks one matrix and cannot replace the universal
trace theorem.

## Remaining mathematical work and LeanCert scope

Pinned Mathlib supplies elementary symmetric/power-sum Newton identities,
block characteristic-polynomial identities, trace/characteristic-coefficient
identities and Cayley–Hamilton. The arbitrary-matrix trace-power bridge is
still substantial mathematical work. The inspected API notes in
[reviews/statement-evidence/API_NOTES.md](reviews/statement-evidence/API_NOTES.md)
state what is present and what remains unproved. No missing bridge may be
replaced by an axiom, an added premise or a one-matrix computation.

The planned numerical certificate is only
`(-8593/823543 : ℝ) < 0`, to be established using kernel LeanCert and materially
consumed in the final contradiction. All matrix, polynomial, derivative and
general trace identities require exact proofs. No interval subdivision,
approximate root computation or numerical eigensolver is planned. This
statement-stage package contains no executed interval certificate.

The frozen statement/source manifest and handoff are under `reviews/`.
Independent review follows the pinned Tau Ceti rubrics as adapted by this
repository's [review protocol](../../../docs/lean/REVIEW.md); neither the
author's checks nor a later agent approval should be described as external
human peer review.
