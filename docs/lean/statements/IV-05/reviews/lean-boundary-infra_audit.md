# IV-05 independent Lean-boundary review

Reviewer: `/root/infra_audit`, OpenAI Codex AI agent independent of per-ID author `/root/statement_design` and shared-model author `/root/inventory`. Phase: `lean-boundary`. Verdict: **approve**.

InputPromise includes n>=1 and weak rational endpoint order, then quantifies every real matrix with each entry independently inside its closed interval. RHS entries likewise range independently over their entire real intervals. Zero widths, arbitrary RHS signs, zero coordinates, reducibility and zero off-diagonal inverse entries remain included.

The pinned Matrix inverse is det-inverse times adjugate and totalizes singular matrices to zero. InverseMMatrix explicitly guards A.det!=0, then NonsingularMMatrix(A inverse) explicitly guards its determinant, requires each off-diagonal entry<=0, and the genuine double inverse entrywise>=0. This is exactly the source nonsingular M-matrix definition, without accidental acceptance through a zero totalized inverse or extra irreducibility/strict-sign assumptions.

IsSolution is existence of actual independent interval A,b with all ordinary real equations A*x=b. Invertibility from InputPromise makes it precisely the original A inverse b solution set. There is no separate hull of the inverse or lost dependence among its entries.

ExactHull universally encloses every solution coordinate and separately requires an attained lower and upper witness for each coordinate. The existential witnesses occur inside each coordinate and endpoint clause, so no common optimizing vector or matrix is required. All endpoints are exact rationals in Fin(inputDimension).

Target quantifies one finite transducer and uniform polynomial bound before every promised input. Its terminal output must be the complete encodeIntervalOutput of that same dimension followed by all lower and upper rational coordinates. Every output bit is real tape data; no semantic decoder substitutes an answer. Runtime is polynomial in complete input bits. Off-promise behavior and promise recognition are unrestricted exactly as in the source; rational endpoint existence alone is not substituted for this machine requirement.

The shared machine is an actual finite TM0 instance: Fin(stateBound+1) control states, Option Bool alphabet, and a fixed transition table over that finite domain. I inspected the pinned TM0 step/init and Tape definitions: a step moves one cell or writes one symbol, input is placed on a finite tape with blank exterior, and the table cannot inspect an unlimited mathematical input in one operation.

RunsWithin requires Nonempty of the actual EvalsToInTime structure, a reached configuration c, step(c)=none, and equality of its complete right-tape suffix to the requested nonblank bit list. EvalsToInTime records genuine iteration and steps<=T. Reachability alone is not terminality; trailing false is a data bit distinct from the blank none. The machine is deterministic and there is no free runtime/evaluator or arithmetic/LP oracle.

PolynomialBound contains a positive natural coefficient and natural exponent, selected before all inputs, with value coefficient*(inputLength+1)^exponent. InputLength is the length of the full explicit binary encoding. The finite machine and bound cannot vary with the input, its conditioning, analytic promise or output.

BinaryEncoding is fixed concrete syntax. Nat.bits is least-significant-first in the pinned source, and binary reverses it, with a one-bit zero special case. The unary prefix encodes bit length, so a scalar has length2L+1, not unary-in-value size. Integer sign and normalized Rat.num/Rat.den are explicit; rational denominator is positive and reduced. Dense matrices enumerate every entry row-major; vectors enumerate their full finite index. Prefix parsing rejects missing/truncated/extra/leading-zero/noncanonical fields and does not evaluate any analytic promise.

The grammar is an injective ordinary binary representation with only linear framing overhead in each scalar bit length; conversion from other signed numerator/positive denominator representations uses ordinary polynomial gcd normalization when needed. This is a mathematical model-correspondence review of the actual explicit definitions, not a claim that universal codec/complexity-translation theorems have been formally proved. Those pending formal lemmas are documented and are not assumptions in Target. The direct encoded-input quantifier covers every rational input and does not require behavior on malformed strings.

I independently compiled fresh FiniteMachine, BinaryEncoding, Controls and both live targets, then both final frozen targets and actual rfl identity checks, into a separate review build. All exited0. Kernel controls check framing, rational normalization/rejection, dense input/output ordering and actual terminal-versus-reached behavior. Target axiom closures contain only propext, Classical.choice, Quot.sound; #assert_statement and #assert_trust kernel passed. Both final preimplementation approval hash bindings remain intact.

The live and frozen per-ID propositions have separate definitions. Both intentionally share the reviewed finite-machine/encoding types; this full import closure is hash-bound below, so frozen reflexivity does not authorize changes to shared semantics. No catalog algorithm is constructed or proved. This report gives independent source/mathematical correspondence review and local macOS kernel checks; it is not external human review, formal proof of the resolution or Linux Comparator execution.

## Bound repository inputs

- `docs/lean/statements/IV-05/IMPLEMENTATION_NOTES.md`: `4858b6892d7f79d33d82306968ce41f0c0d261998df64342390d64cc289fae30`
- `docs/lean/statements/IV-05/NUMERICAL_TARGETS.md`: `a70e3008bfa3cfae8b068fc3af690a761ee44f75bb46a2fb2a8d101ede2ff931`
- `docs/lean/statements/IV-05/ORIGINAL.md`: `09f68840d5c42b3b101532620a8900a7253f6f881bfa59ad99e80ff21c16a87c`
- `docs/lean/statements/IV-05/reviews/lean-boundary-infra-audit-evidence/NLA-Computation-BinaryEncoding.log`: `2a3954627795f50423fd88b74045fed1aa6fcc709aa93aa4113bc4d4ac5d9a30`
- `docs/lean/statements/IV-05/reviews/lean-boundary-infra-audit-evidence/NLA-Computation-Controls.log`: `602bf0a947742e88f21e4e7a4ffd1523399e396a6a3e698a56fc41d2825da6cd`
- `docs/lean/statements/IV-05/reviews/lean-boundary-infra-audit-evidence/NLA-Computation-FiniteMachine.log`: `2a3954627795f50423fd88b74045fed1aa6fcc709aa93aa4113bc4d4ac5d9a30`
- `docs/lean/statements/IV-05/reviews/lean-boundary-infra-audit-evidence/NLA-Statements-IV05.log`: `601aed116be63622488a634495b584793dc38c3f04c1b64c3de55b999ddc61bc`
- `docs/lean/statements/IV-05/reviews/lean-boundary-infra-audit-evidence/Reviewed-IV05.log`: `8ad71faf714e84770cd23ee901e2e95e3401d1ecf5dc33d6a7ec623361478a77`
- `docs/lean/statements/IV-05/reviews/lean-boundary-infra-audit-evidence/identity.log`: `2a3954627795f50423fd88b74045fed1aa6fcc709aa93aa4113bc4d4ac5d9a30`
- `docs/lean/statements/IV-05/source-lock.json`: `d4c8f5f39f6485b54bc012165393a0ab45717911a5f7aaf4a6e1d8d87b7d8446`
- `docs/lean/statements/computational-model/IMPLEMENTATION_NOTES.md`: `46d47e5f1ab70ddb0659e159d423da6ac035d40e74efabc510a92fd7377d4e5b`
- `docs/lean/statements/computational-model/MODEL_SPECIFICATION.md`: `2190ec99aceb23943c6ece7f270ad31c535c8cab594f3e755e2ed11110d0311c`
- `intervals-and-absolute-value-equations/IV-05/README.md`: `09f68840d5c42b3b101532620a8900a7253f6f881bfa59ad99e80ff21c16a87c`
- `lean-statements/NLA/Computation/BinaryEncoding.lean`: `d494ffb15274500ea5c06c480c2b2032a48390533f7171b4ed993d947c44ee6a`
- `lean-statements/NLA/Computation/Controls.lean`: `3ee7958d508bbcef064b1c23e4826c26535de7ea1115795c941acc7f0e763cfc`
- `lean-statements/NLA/Computation/FiniteMachine.lean`: `7c8b2a8e88220b3a1a66bf9c9748ee2213b155dd239809654240095180918d9d`
- `lean-statements/NLA/Statements/IV05.lean`: `a75a5713d7c6672efa85a16e08615b302cde068da7c7bd2218030b07abf51807`
- `lean-statements/NLA/Statements/Infrastructure.lean`: `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37`
- `lean-statements/Reviewed/IV05.lean`: `85b98d4c3eb851819bc919737aaf33a4f91c91c59e826bded20ca96064e3af9e`
- `lean-statements/lake-manifest.json`: `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8`
- `lean-statements/lakefile.toml`: `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40`
- `lean-statements/lean-toolchain`: `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71`

## Inspected pinned dependency sources

- `Mathlib/Computability/TuringMachine/PostTuringMachine.lean` at `0df444a360eaa60ab8c11dca51a86af692955474`: `2380a758451146b8575fe10d84b8c5c71c0a190e572d84674d4782ce59a79854`
- `Mathlib/Computability/TuringMachine/Tape.lean` at `0df444a360eaa60ab8c11dca51a86af692955474`: `76144efd656fa16485735ce381a2b1c98feb95893a8bc60addf6ad009a043f13`
- `Mathlib/Computability/StateTransition.lean` at `0df444a360eaa60ab8c11dca51a86af692955474`: `eceb96a26dccbd8f8abcd83874539b49b8b7e797f195a864cff85c1bbe8476b2`
- `Mathlib/Data/Nat/Bits.lean` at `0df444a360eaa60ab8c11dca51a86af692955474`: `a11e29552e7962e7b7098a68a1eba9203e97f186ccec6e6ce6f52dd320745a3d`
- `Mathlib/Data/Rat/Defs.lean` at `0df444a360eaa60ab8c11dca51a86af692955474`: `e644776b8813e3764493563b13beac92092a98854d017081f496c329078d2c1f`
- `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean` at `0df444a360eaa60ab8c11dca51a86af692955474`: `1ee785b6ebd213ad2ed971bf3c804afee8cc6ce52be69e63572b4cf1bdb5e880`
