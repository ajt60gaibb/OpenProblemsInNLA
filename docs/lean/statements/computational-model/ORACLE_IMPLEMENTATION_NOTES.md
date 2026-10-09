# Concrete verifier and promised-oracle extension

Author: OpenAI Codex AI agent `/root/inventory`.

This implements the previously approved model in four new modules:
`NLA.Computation.QueryTape`, `Complexity`, `OracleMachine`, and `OracleControls`.
The reviewed ordinary machine, binary encoders and ordinary control modules
are unchanged. No AV-02 target, NP-completeness result or reduction algorithm
is asserted. Independent review of these definitions remains required.

`InNP` uses the actual finite ordinary verifier, the fixed explicit pair
encoder, one polynomial certificate-length bound, and one polynomial runtime
bound. It requires the verifier to return a Boolean on every encoded pair,
including overly long certificates. Membership uses an actual accepting run
on some bounded-length binary certificate. `InCoNP` uses complement membership.
Many-one reduction definitions require actual transducer outputs; a promised
variant also requires a legal output for every source word.

The oracle program has a finite state set, fixed three-symbol tape alphabet,
three physical tapes and a finite table depending only on the current state
and three head symbols. Work instructions perform at most one move/write on
each tape. Initial state is zero; only the main tape initially contains input.
Only an explicit query instruction may call the oracle. It reads the current
query suffix, changes to a fixed yes/no continuation state and preserves all
tapes. The successful halt instruction costs a step. All subsequent halted
or failed states are absorbing.

`QueryTape` decodes finite lists of actual symbols, ignores trailing blanks
and rejects an internal blank followed by a later bit. Its proof of invariance
under appending blanks makes this a well-defined operation on Mathlib's
quotient tape representation. There is no choice of an arbitrary query
function or encoded mathematical input. The general `read_input` theorem
verifies the exact word returned for every properly encoded binary tape.
Extraction occurs only as part of the conventional unit-cost oracle-query
interface; ordinary machines receive no free string operation.

A malformed query goes to a distinct failed tag; it cannot succeed merely
because an output bit is already on the main tape. A correctly represented
word outside the problem's promise is a different case: the oracle may answer
arbitrarily, and the reduction's legality condition forbids making that call
in every required run.

`queryTrace` derives the chronological list of queries directly from the
actual prefix of execution. Each event records its time, concrete pre-query
configuration and word. It is observational metadata, not a register or input
that the machine can read. `RunsWithin` uses one time witness for all four
requirements: bounded actual execution, successful halt, exact main-tape
output and legality of every event in that same trace.

`PolynomialOracleReduces` places the machine and bound before every compatible
oracle and input. Correctness holds for all compatible oracles, and the same
bound counts every source word. `OracleNPHard` universally quantifies source
NP languages. The target must instantiate its actual mathematical legal/yes
languages; no selected source problem or assumed completeness theorem replaces
that quantifier. No statement requires a promise-recognition algorithm.

Kernel controls cover writing before querying, the exact query trace,
different charged yes/no paths and outputs, a successful run with a legal
query, rejection of that trace by an empty promise, tape preservation during
a query, a malformed tape with an apparent main output, absence of an actual
call on malformed input, and absorbing terminal tags. The malformed-input
control tests a concrete configuration directly to avoid redundant expansion
of a long initialization trace; it tests the exact failure rule without
altering the machine semantics. No `native_decide`, custom axiom or `sorry`
is used.

Author-local pinned macOS compilation evidence is recorded in
`/tmp/nla-computation-evidence/oracle-final-inputs.json`. This is kernel
elaboration and control evidence, not a Linux Comparator run or a catalog
proof. The root campaign must route `NLA.Computation.OracleControls` into CI.
General codec inverses, simulation equivalences and source-language
completeness proofs remain separate future proof work; none is assumed here.
