# Computational model: independent specification review

Reviewer: /root/statement_design (OpenAI Codex AI agent), independent of author /root/inventory.
Date: 2026-09-28. Verdict: **approve** on the final source hashes below.
The two oracle clarifications requested during review are resolved.

## Checks and resolved findings

1. Ordinary machines have a fixed three-symbol alphabet and finite state type Fin(s+1). A function on the resulting finite state/symbol domain is a finite table; no infinite-data symbol, register, arbitrary evaluator or cost function enters the model. The inspected TM0 step performs exactly one move or one write.

2. RunsWithin demands both a bounded actual transition trace and terminality at its final concrete configuration, with an injective exact binary output convention. Merely reaching a state or reaching Option.none cannot be confused with Boolean acceptance.

3. The framed binary grammar is prefix-decodable, canonical, and linear in underlying bit lengths up to fixed overhead. It explicitly handles zero, signs, positive denominators, row-major dimensions, exact field consumption and IV05 endpoint output. Arithmetic normalization and efficient parsing/model equivalence remain honest implementation correspondence obligations, not free algorithmic steps.

4. The direct encoded-input decision/function statements put the finite machine and polynomial constants before every instance. AV01 includes all rational instances and infinite solution sets are negative. IV05 preserves its inverse-M promise, exact rational endpoint enclosure plus separate attainment, and unrestricted off-promise behavior.

5. The NP definition uses a concrete finite Boolean verifier with polynomial binary certificate length and polynomial runtime on encoded pairs. The certificate is a bit string, not a semantic relation. Universal NP-hardness can therefore be stated without first proving MAX-CUT completeness, constructing a reduction, or implementing an LP solver.

6. The oracle extension explicitly initializes all tapes and the initial state, reads successful output only from the main tape, and uses a unique concrete query word encoded on the query tape. Its finite transition table cannot inspect an entire input in one ordinary step; only the intended oracle query receives a unit-cost answer.

7. Requested clarification 1 is resolved in final Section 5: Fin(s+1) state zero, input on the main tape, blank additional work/query tapes, designated head origins, and the same exact output convention are explicit.

8. Requested clarification 2 is resolved in final Section 5: malformed-query failure is a tagged failure terminal distinct from successful halt. It never satisfies accepted output even if current tape bits resemble a Boolean answer. A well-formed but off-promise query remains distinct and is prohibited by legality.

9. Hardness quantifiers are in the required order: every NP language, then one reduction and polynomial bound, then every compatible oracle and every input, with successful output, time and legality of every query in the same run property. There is no favorable-oracle choice or hidden promise recognizer.

10. The optional finite TM2 route is accurately qualified: all stack alphabets must be finite and replacing the selected TM0 semantics requires a reviewed cost correspondence. The inspected FinTM2 record only requires the input alphabet to be finite; its composition declaration is proof_wanted. The inspected Batteries mechanism records unmet propositions without proving them or introducing a target axiom.

11. All source-audit hashes match the pinned local sources, and the audit correctly limits its API search claims. Shared model changes must reopen importing boundary reviews; frozen target names cannot conceal changed meanings.

## Bound inputs

- docs/lean/statements/computational-model/MODEL_SPECIFICATION.md: 2190ec99aceb23943c6ece7f270ad31c535c8cab594f3e755e2ed11110d0311c
- docs/lean/statements/computational-model/source-audit.json: 7e8efd4460378bb329cdd941d631c13126881569c142fd017404a4e44a476d10
- lean-statements/lakefile.toml: 1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40
- lean-statements/lake-manifest.json: a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8
- lean-statements/lean-toolchain: 3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71
- docs/lean/statements/AV-01/NUMERICAL_TARGETS.md: d524be200a4238cc2b23c86eb08523bb76fe4c6accc5dac204451f2cc335b3cf
- docs/lean/statements/AV-02/NUMERICAL_TARGETS.md: 26dba9081ffffa9d4b46d2feee2749992fb659bc2e9d12afdaeabb0a672da7da
- docs/lean/statements/IV-05/NUMERICAL_TARGETS.md: a70e3008bfa3cfae8b068fc3af690a761ee44f75bb46a2fb2a8d101ede2ff931

## Pinned source identity

All files listed in source-audit.json were independently SHA-256 checked against the local pinned Mathlib/Batteries checkouts. Key API definitions read directly: TM0 Machine/Stmt/step/init/eval; EvalsTo and EvalsToInTime; FinTM2 and its proof_wanted composition; Encoding and encodeNat; Batteries ProofWanted placeholder semantics.

## Limits

Independent AI-agent mathematical/model specification review only. No shared Lean model implementation or encoding/simulation proof is present, so this is not a final Lean-boundary review. The audited sources and key API definitions were inspected; the bounded absence search was assessed as a qualified report, not reclassified as a proof of absence. No LP algorithm, NP-hardness theorem, mathematical catalog target, runtime bound or Linux Comparator execution is certified.
