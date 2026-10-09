# AV-01 independent Lean-boundary review

Reviewer: `/root/infra_audit`, OpenAI Codex AI agent independent of per-ID author `/root/statement_design` and shared-model author `/root/inventory`. Phase: `lean-boundary`. Verdict: **approve**.

IsSolution universally tests every coordinate of every real n-vector with the exact rational-to-real matrix/RHS embeddings, full matrix row sum, and componentwise real absolute value. No real solutions are replaced by rational ones.

HasExactSolutionCount is Nonempty of an equivalence between Fin(2^n) and the complete solution subtype. It counts exactly the distinct real points and enforces finiteness, so infinite solution sets are negative without any finite-solution promise.

Target requires every AVInput with n>=1, without regularity, nonsingularity, sign, genericity or boundedness restrictions. One actual Boolean tape output is true if and only if the complete cardinality predicate holds. Determinism prevents different possible answers to the same encoded input.

This states the resolved affirmative membership-in-P branch of the complete original classification question, as independently specified. It does not replace computational complexity by the LP characterization, require solution enumeration, or assert a separation of P from NP/coNP. Full original history and source credit remain preserved.

The shared machine is an actual finite TM0 instance: Fin(stateBound+1) control states, Option Bool alphabet, and a fixed transition table over that finite domain. I inspected the pinned TM0 step/init and Tape definitions: a step moves one cell or writes one symbol, input is placed on a finite tape with blank exterior, and the table cannot inspect an unlimited mathematical input in one operation.

RunsWithin requires Nonempty of the actual EvalsToInTime structure, a reached configuration c, step(c)=none, and equality of its complete right-tape suffix to the requested nonblank bit list. EvalsToInTime records genuine iteration and steps<=T. Reachability alone is not terminality; trailing false is a data bit distinct from the blank none. The machine is deterministic and there is no free runtime/evaluator or arithmetic/LP oracle.

PolynomialBound contains a positive natural coefficient and natural exponent, selected before all inputs, with value coefficient*(inputLength+1)^exponent. InputLength is the length of the full explicit binary encoding. The finite machine and bound cannot vary with the input, its conditioning, analytic promise or output.

BinaryEncoding is fixed concrete syntax. Nat.bits is least-significant-first in the pinned source, and binary reverses it, with a one-bit zero special case. The unary prefix encodes bit length, so a scalar has length2L+1, not unary-in-value size. Integer sign and normalized Rat.num/Rat.den are explicit; rational denominator is positive and reduced. Dense matrices enumerate every entry row-major; vectors enumerate their full finite index. Prefix parsing rejects missing/truncated/extra/leading-zero/noncanonical fields and does not evaluate any analytic promise.

The grammar is an injective ordinary binary representation with only linear framing overhead in each scalar bit length; conversion from other signed numerator/positive denominator representations uses ordinary polynomial gcd normalization when needed. This is a mathematical model-correspondence review of the actual explicit definitions, not a claim that universal codec/complexity-translation theorems have been formally proved. Those pending formal lemmas are documented and are not assumptions in Target. The direct encoded-input quantifier covers every rational input and does not require behavior on malformed strings.

I independently compiled fresh FiniteMachine, BinaryEncoding, Controls and both live targets, then both final frozen targets and actual rfl identity checks, into a separate review build. All exited0. Kernel controls check framing, rational normalization/rejection, dense input/output ordering and actual terminal-versus-reached behavior. Target axiom closures contain only propext, Classical.choice, Quot.sound; #assert_statement and #assert_trust kernel passed. Both final preimplementation approval hash bindings remain intact.

The live and frozen per-ID propositions have separate definitions. Both intentionally share the reviewed finite-machine/encoding types; this full import closure is hash-bound below, so frozen reflexivity does not authorize changes to shared semantics. No catalog algorithm is constructed or proved. This report gives independent source/mathematical correspondence review and local macOS kernel checks; it is not external human review, formal proof of the resolution or Linux Comparator execution.

## Bound repository inputs

- `docs/lean/statements/AV-01/IMPLEMENTATION_NOTES.md`: `f0b5b644b5c57ef207f08d078c0921a7841837ba1bfe1873179d0a7d00848a02`
- `docs/lean/statements/AV-01/NUMERICAL_TARGETS.md`: `d524be200a4238cc2b23c86eb08523bb76fe4c6accc5dac204451f2cc335b3cf`
- `docs/lean/statements/AV-01/ORIGINAL.md`: `68205f4476868847a9332d5ab294d062882302f203e6903f4da3c43f61f5f091`
- `docs/lean/statements/AV-01/reviews/lean-boundary-infra-audit-evidence/NLA-Computation-BinaryEncoding.log`: `2a3954627795f50423fd88b74045fed1aa6fcc709aa93aa4113bc4d4ac5d9a30`
- `docs/lean/statements/AV-01/reviews/lean-boundary-infra-audit-evidence/NLA-Computation-Controls.log`: `602bf0a947742e88f21e4e7a4ffd1523399e396a6a3e698a56fc41d2825da6cd`
- `docs/lean/statements/AV-01/reviews/lean-boundary-infra-audit-evidence/NLA-Computation-FiniteMachine.log`: `2a3954627795f50423fd88b74045fed1aa6fcc709aa93aa4113bc4d4ac5d9a30`
- `docs/lean/statements/AV-01/reviews/lean-boundary-infra-audit-evidence/NLA-Statements-AV01.log`: `5db9e7fb23c18350ee16609b458496904e2e3088a7adff1cd400ddc22608cc32`
- `docs/lean/statements/AV-01/reviews/lean-boundary-infra-audit-evidence/Reviewed-AV01.log`: `89d0eacddcdfa46bb5b318c67fee6c1befbbaf7fed37d56531e2ee7a4eda6946`
- `docs/lean/statements/AV-01/reviews/lean-boundary-infra-audit-evidence/identity.log`: `2a3954627795f50423fd88b74045fed1aa6fcc709aa93aa4113bc4d4ac5d9a30`
- `docs/lean/statements/AV-01/source-lock.json`: `95cc1b39ee8f32841f675eb552af99cd7bb244f3e2a6f6c429345c1cca917d60`
- `docs/lean/statements/computational-model/IMPLEMENTATION_NOTES.md`: `46d47e5f1ab70ddb0659e159d423da6ac035d40e74efabc510a92fd7377d4e5b`
- `docs/lean/statements/computational-model/MODEL_SPECIFICATION.md`: `2190ec99aceb23943c6ece7f270ad31c535c8cab594f3e755e2ed11110d0311c`
- `intervals-and-absolute-value-equations/AV-01/README.md`: `68205f4476868847a9332d5ab294d062882302f203e6903f4da3c43f61f5f091`
- `lean-statements/NLA/Computation/BinaryEncoding.lean`: `d494ffb15274500ea5c06c480c2b2032a48390533f7171b4ed993d947c44ee6a`
- `lean-statements/NLA/Computation/Controls.lean`: `3ee7958d508bbcef064b1c23e4826c26535de7ea1115795c941acc7f0e763cfc`
- `lean-statements/NLA/Computation/FiniteMachine.lean`: `7c8b2a8e88220b3a1a66bf9c9748ee2213b155dd239809654240095180918d9d`
- `lean-statements/NLA/Statements/AV01.lean`: `34bc564a472d6cf0fea282c7b2c40fa1f909305c2b8a9360fb086b0ffa9b7732`
- `lean-statements/NLA/Statements/Infrastructure.lean`: `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37`
- `lean-statements/Reviewed/AV01.lean`: `576c67a10299fe08ab851594194120dc8acbe725a8f4a76628d98c70eb3f8e4a`
- `lean-statements/lake-manifest.json`: `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8`
- `lean-statements/lakefile.toml`: `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40`
- `lean-statements/lean-toolchain`: `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71`

## Inspected pinned dependency sources

- `Mathlib/Computability/TuringMachine/PostTuringMachine.lean` at `0df444a360eaa60ab8c11dca51a86af692955474`: `2380a758451146b8575fe10d84b8c5c71c0a190e572d84674d4782ce59a79854`
- `Mathlib/Computability/TuringMachine/Tape.lean` at `0df444a360eaa60ab8c11dca51a86af692955474`: `76144efd656fa16485735ce381a2b1c98feb95893a8bc60addf6ad009a043f13`
- `Mathlib/Computability/StateTransition.lean` at `0df444a360eaa60ab8c11dca51a86af692955474`: `eceb96a26dccbd8f8abcd83874539b49b8b7e797f195a864cff85c1bbe8476b2`
- `Mathlib/Data/Nat/Bits.lean` at `0df444a360eaa60ab8c11dca51a86af692955474`: `a11e29552e7962e7b7098a68a1eba9203e97f186ccec6e6ce6f52dd320745a3d`
- `Mathlib/Data/Rat/Defs.lean` at `0df444a360eaa60ab8c11dca51a86af692955474`: `e644776b8813e3764493563b13beac92092a98854d017081f496c329078d2c1f`
