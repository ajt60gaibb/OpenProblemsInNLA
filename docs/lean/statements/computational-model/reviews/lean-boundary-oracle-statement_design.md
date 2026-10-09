# NP and promised-oracle model: independent final boundary review

Reviewer: /root/statement_design (OpenAI Codex AI agent), 2026-09-28.
Verdict: **approve** for the scope and exact bytes below.

## Definition fidelity

1. All four new source files and the implementation notes were read against the final approved MODEL_SPECIFICATION. The ordinary FiniteMachine and BinaryEncoding dependencies retain their previously approved bytes; their actual finite-state step, terminal output and fixed pair grammar remain the only ordinary verifier/reduction semantics.

2. QueryTape.decodeSymbols decodes a contiguous sequence of nonblank bit symbols, accepts trailing blanks and rejects an internal blank followed by any later bit. A blank-only suffix represents exactly the empty word. False bit symbols are some false and therefore cannot be confused with blank none.

3. The pinned ListBlank representation is a quotient by finite trailing-blank extension. The general decodeSymbols_append_blanks proof supplies exactly the invariant required by the inspected ListBlank.liftOn API. Thus readSuffix is independent of quotient representatives, not an arbitrary choice of a list. read_input proves proper encoded words are recovered for every binary word.

4. The parser matches the approved equality-based query convention: a successful word has exactly its bit symbols followed by blanks, and every such suffix is decoded. This correspondence was checked structurally from the parser; a separate general Lean if-and-only-if theorem is not claimed present.

5. InNP quantifies one actual finite ordinary verifier, a polynomial certificate-length bound and a polynomial time bound. It requires Boolean termination on every encoded pair, including overlong certificates, and uses actual bounded true-output execution for membership witnesses. No free semantic verifier relation appears. InCoNP is complement membership.

6. InP, ordinary many-one and promise-many-one reductions similarly require actual terminal machine output in the fixed polynomial budget. The promised variant additionally requires every output word to be legal. No arbitrary reduction map with an assumed cost is substituted.

7. OracleMachine has Fin(stateBound+1) control and exactly three tapes over Option Bool. Its table observes only control and the three current head symbols. Each work instruction has at most one move/write per tape and fixed finite next state, with optional no-ops. No full configuration, query log or unbounded mathematical value is available to its finite program.

8. Initialization uses state zero, the given word only on the main tape, blank work/query tapes and a running tag. Only an explicit query instruction invokes the oracle, on QueryTape.read of the actual current query suffix. It leaves all tapes unchanged and selects a fixed yes/no continuation. Constructing, moving to and clearing a query use counted work instructions.

9. The status type distinguishes running, halted and failed. Malformed query decoding sets failed; successful halt is a separate counted instruction. Both terminal statuses absorb, but RunsWithin requires halted specifically, so failure cannot accept a preexisting main-tape output bit. A valid off-promise word is a separate case governed by query legality.

10. queryTrace is computed from List.range t and the actual run configuration at each time before t. It records only actual running well-formed query instructions, with the exact time, pre-query state and word. This is observational trace data, not machine memory. No actual call before successful halt can escape the trace; malformed queries cannot reach successful halt.

11. Oracle RunsWithin uses one witness t for the bound, successful status, exact main output and legality of every event from that same execution prefix. Absorbing terminal states ensure later padded trace time does not add hidden calls. Output uses the same injective nonblank-bit tape convention as the ordinary model.

12. Compatible requires correct yes/no behavior on every legal word and imposes no behavior off promise. PolynomialOracleReduces places the same machine and bound before every compatible oracle and every source word, retaining adaptive queries and every-query legality. The definition cannot exploit one favorable compatible oracle or oracle-dependent runtime. Compatible oracles exist classically for any legal/yes sets, so this universal requirement is not vacuous.

13. OracleNPHard universally quantifies all languages satisfying the concrete InNP definition. Legal and yes are parameters only to reusable problem-class definitions and must be instantiated by actual fixed mathematical predicates in AV02. No source completeness theorem, target promise recognizer or LP/spectral oracle is silently assumed.

14. OracleControls provides kernel checks of writing before a call, charged yes/no paths, exact trace/output, legal and illegal query traces, unchanged tapes, malformed-query failure despite an apparent output, no call on malformed data, and absorbing tags. The examples are correctly scoped as operational regression proofs, not general simulation, codec inversion or hardness proofs.

15. The final StatementControls.lean imports OracleControls, so the new operational controls enter the CI control root. That exact wiring file is bound. Its independent ExactRealControls import is outside this oracle-model review scope; no claim about the unrelated exact-real model follows from this approval.

16. Author source/pin/model/notes/log hashes all matched. Retained independent root receipts also match the exact sources and report exit zero for all four modules and StatementControls. Printed InNP and OracleNPHard closures contain only propext, Classical.choice and Quot.sound. This reviewer inspected the evidence but did not separately execute Lean or assert a Linux run.

17. General codec inversion, polynomial simulation between machine models, NP-completeness theorems and concrete reductions remain future proof work, as documented. None is accepted as a premise inside these actual definitions. No AV02 target, computational classification theorem or catalog proof is approved by this model-only report.

## Pinned external definitions inspected

- Mathlib/Computability/TuringMachine/Tape.lean: 76144efd656fa16485735ce381a2b1c98feb95893a8bc60addf6ad009a043f13; BlankExtends, BlankRel, ListBlank, liftOn, mk and finite-tape primitives; quotient invariant inspected directly.
- Mathlib/Computability/TuringMachine/PostTuringMachine.lean: 2380a758451146b8575fe10d84b8c5c71c0a190e572d84674d4782ce59a79854; Finite current-symbol move/write machine step and initialization; ordinary base rereviewed in prior bound report.
- Mathlib/Computability/StateTransition.lean: eceb96a26dccbd8f8abcd83874539b49b8b7e797f195a864cff85c1bbe8476b2; Actual finite iteration and time-bound witness used by the ordinary verifier.

## Bound inputs

- docs/lean/statements/computational-model/MODEL_SPECIFICATION.md: 2190ec99aceb23943c6ece7f270ad31c535c8cab594f3e755e2ed11110d0311c
- docs/lean/statements/computational-model/ORACLE_IMPLEMENTATION_NOTES.md: 2d241730aa94c93bf66c3ddd445ab0a9d17e9e957b34b0b068a99d0863b9b2fd
- docs/lean/statements/computational-model/source-audit.json: 7e8efd4460378bb329cdd941d631c13126881569c142fd017404a4e44a476d10
- docs/lean/statements/verification/2026-09-28-oracle-model/NLA-Computation-Complexity.lean.log: e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
- docs/lean/statements/verification/2026-09-28-oracle-model/NLA-Computation-OracleControls.lean.log: 505821a2d890f0e31311b0f534799a6a3fd9baf41d5dab39f56d8ad0dd30fd9a
- docs/lean/statements/verification/2026-09-28-oracle-model/NLA-Computation-OracleMachine.lean.log: e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
- docs/lean/statements/verification/2026-09-28-oracle-model/NLA-Computation-QueryTape.lean.log: e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
- docs/lean/statements/verification/2026-09-28-oracle-model/StatementControls.lean.log: e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
- docs/lean/statements/verification/2026-09-28-oracle-model/receipt.json: 231604cb946149a306f71ebdf226cd5f4b3b57f2361d06366e422758c99fc528
- lean-statements/NLA/Computation/BinaryEncoding.lean: d494ffb15274500ea5c06c480c2b2032a48390533f7171b4ed993d947c44ee6a
- lean-statements/NLA/Computation/Complexity.lean: 0ad5ee64d5ef0b77f5531b31bb1b69a1a668c556cbd79b42fea7b6f108275c88
- lean-statements/NLA/Computation/FiniteMachine.lean: 7c8b2a8e88220b3a1a66bf9c9748ee2213b155dd239809654240095180918d9d
- lean-statements/NLA/Computation/OracleControls.lean: 3a33851e293024dd03d5d2fecf315418679d517c352d8be4a9dec9f8b17ac4a3
- lean-statements/NLA/Computation/OracleMachine.lean: 83d5ce8087aeb2acaf6618d6e4e38aa622ff895ff895619e7d934a4a3960cd6c
- lean-statements/NLA/Computation/QueryTape.lean: 835806202af142538cf57942f5512a065178bad57d725b82db739ca1cad05b83
- lean-statements/StatementControls.lean: 873152e48807afe752cd9eac0f3f72f3bd44323bbf87695ae5b0156a7e102b8a
- lean-statements/lake-manifest.json: a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8
- lean-statements/lakefile.toml: 1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40
- lean-statements/lean-toolchain: 3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71

## Limits

Independent AI-agent final source/model fidelity review, independent of author /root/inventory. Approval covers the concrete NP, ordinary/promise reduction and three-tape oracle definitions plus operational controls and CI wiring. It does not prove class equivalence, codec inversion, simulation complexity, a catalog target or an independently executed kernel/CI result. ExactRealControls is outside this review scope.
