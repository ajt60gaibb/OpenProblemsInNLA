# Ordinary computation and encoding implementation

Author: OpenAI Codex AI agent `/root/inventory`.

The ordinary finite-machine and binary-encoding portion of the approved
`MODEL_SPECIFICATION.md` is implemented in:

- `lean-statements/NLA/Computation/FiniteMachine.lean`
- `lean-statements/NLA/Computation/BinaryEncoding.lean`
- `lean-statements/NLA/Computation/Controls.lean`

Both independent specification reviews were checked against their final input
and report hashes before writing these modules. Final independent source and
mathematical reviews of this implementation are still required. No catalog
target, NP class or oracle-machine extension is implemented by these files.

## Concrete semantic boundary

`FiniteMachine` contains a natural state bound and an actual finite TM0 table.
The tape alphabet is `Option Bool`, and the control states are
`Fin (stateBound + 1)`. Initial state zero and the input tape are Mathlib's actual
initialization. `RunsWithin` requires an actual bounded iteration of its fixed
step function, terminality of the reached configuration, and the complete
nonblank-bit output suffix. It does not accept an arbitrary evaluator, runtime
function, real arithmetic instruction or solver callback. `PolynomialBound`
has a positive natural coefficient and a natural exponent; its value is
`coefficient * (inputLength + 1)^exponent`.

Natural encodings use MSB-first bits, zero `[false]`, and the exact unary
bit-length prefix specified in the reviewed model. Signed integers reject
negative zero. Rationals use normalized signed numerators and positive coprime
denominators; parsing rejects zero denominators and unreduced input. These are
fixed definitions, not existentially chosen encoders.

Dense matrix coefficients are written row by row, including every zero. The
three input structures implement AV-01, AV-02 and IV-05 field order. The IV-05
output contains its dimension followed by all lower and all upper endpoints.
Decoders consume the entire word and reject extra suffixes. Parser positivity
of a matrix dimension, positivity of the AV-02 threshold, endpoint ordering,
regularity and inverse-M status are deliberately left to the problem's original
semantic domain. In particular, accepting the syntax of a negative threshold
does not make it a legal AV-02 oracle query.

`parseRats` checks that the requested field count is no larger than the
remaining word length before recursion. This prevents an enormous encoded
dimension from allocating an enormous missing matrix. The general proved
`parseRats_length` theorem guarantees the exact coefficient count on every
successful parse. Matrix/vector reconstruction uses `getD`; after the exact
count check all legal coordinate indices are in range, so its fallback zero
does not supply omitted data. The parser reads syntax only and performs no
analytic promise test.

## Kernel controls and evidence

`Controls.lean` proves the exact natural-prefix length formula and recovery of
the length prefix for every length. Its regression examples cover zero and
negative numbers, a multiple-byte numeral, missing separators, truncation,
leading zeros, negative zero, denominator zero, unreduced fractions, zero's
canonical denominator, impossible field counts, row-major matrix order, all
interval input/output fields and extra suffix rejection. It also shows that
syntax parsing does not secretly decide the analytic domain.

Machine controls prove that an immediately halted machine preserves its input
at zero transitions, that a trailing zero output bit is not a blank, and that
zero-step reachability for a moving machine does not imply terminality. These
are kernel proofs, including ordinary `decide` for finite examples; no
`native_decide`, axiom or `sorry` is used. LeanCert trust is explicitly kernel in
the control module. No numerical inequality needed an interval certificate.

Local compilation uses the pinned Lean 4.33.1 and the exact pinned Mathlib and
LeanCert dependencies. Author-local macOS logs and source hashes are in
`/tmp/nla-computation-evidence/`. This is elaboration and regression evidence,
not a Linux Comparator run or a proof of a catalog target. The campaign root
must route `NLA.Computation.Controls` into CI's checked imports before claiming
that CI checks this new standalone module.

## Remaining correspondence proofs and extensions

The files do not assume universal encode/decode inversion, polynomial-time
syntax recognition, polynomial equivalence to other machine/encoding models,
an LP algorithm or complexity closure theorem. General codec inversion and
bit-length/translation theorems beyond the listed elementary lemmas are still
to be proved when the campaign needs formal correspondence results. The
definitions themselves contain no unproved premise standing in for any of
these theorems. Concrete regression examples are not universal codec proofs.

The separately reviewed NP certificate semantics and tagged-failure
three-tape oracle model remain to be implemented before AV-02. This ordinary
module does not export a unit-cost oracle. No changes were made here to
per-problem metadata, generated Comparator identities or canonical pages.
