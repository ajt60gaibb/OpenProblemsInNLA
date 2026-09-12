# FR-12 author proof completion and final-review handoff

**The complete seven-export formal proof is implemented and passes fresh local Lean checks.** Two independent final referees and actual Linux Comparator/default-kernel verification remain pending. This is the author's handoff, not an independent approval. No canonical status, commit, push or PR has been changed.

Mathematical proof and Lean formalization: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with substantial AI-agent assistance. Ferber, Jain and Zhao retain the original conjecture and upper-bound attribution. No human peer review or new historical-priority certification is claimed.

## Approved immutable statements

Both independent statement approvals precede implementation in `verification/proof-start.json`. The complete proof freeze `reviews/proof-freeze.json` has SHA256 `c65d4deaa3e02af8c20a584dd81b944dbdc72f262e326630e115e5fc9070aa87`, binding 74 project files and four original source files. All 19 initial frozen inputs, original targets, configuration and pins remain byte-identical.

The seven public signatures match the frozen Challenge up to the unused forall binder spelling `hn` versus `_hn` in `counting_semantics`. This is an alpha-renaming only; its original `1≤n` premise remains intact. No Challenge byte changed. The Solution comment clarifies that `k+2` is the inner natural exponent and the outer exponent is real; the reviewed numerical statement was already correct. The retained statement-stage README describes its historical phase and must be archived/refreshed during later candidate packaging.

## Complete proof and computational reductions

`Semantics.lean` injects the actual matrix subtype into Boolean entry arrays, proving finiteness in every dimension. It proves equivalence to Mathlib's real Hadamard notion in every positive dimension using the actual entry-unitary and Gram theorems. Thus `Nat.card` counts exactly the original individual labeled sign matrices and cannot conceal an infinite set. Actual row inner products give injectivity of the row map when n≥1.

`Doubling.lean` implements the approved restricted matching construction with a top block `(A_i,B_i)` and bottom block `(A_(σ i),−B_(σ i))`. Every sign and every Gram entry is proved after the actual row/column reindexing. The two top column halves recover A and B; the bottom first half and proved row injectivity recover σ. Cardinality of this actual injection gives `m! H(m)² ≤ H(2m)`. No quotient, fiber-size assumption or all-matching enumeration is used. The source's stronger `(2m−1)!!` recurrence is outside the exports; this smaller factor proves the same requested asymptotic lower bound.

`Growth.lean` constructs an actual order-one Hadamard matrix and proves positivity for every power-of-two order by the established recurrence. It derives `r^r ≤ (2r)!` from Mathlib's actual finite factorial inequality. At `r=2^(k+1)`, this is an exact real-power bound for `(2^(k+2))!`.

The lower-bound proof is a direct induction on the real exponential inequality, avoiding logarithms of the count and asymptotic factorial estimates. The two squared induction exponents plus the factorial exponent combine by exact algebra into `2^(k+3)(k+1)(k+2)/8`. This proves the exact manuscript bound `2^(2^(k+2) k(k+1)/8) ≤ H(2^(k+2))` for every natural k, including k=0. All scalar casts, nonnegative factors and original counts are explicit.

Only the final comparison uses the actual base-two logarithm, with `log(2^(k+2))/log 2=k+2` proved from `Real.log_pow` and log 2>0. For every positive real C, Archimedean choice gives k>16C+2. An exact polynomial inequality then makes the proved lower exponent strictly larger than C·n·log₂n. The resulting order is proved positive and divisible by four, giving the complete unconditional negation of the canonical conjecture. No fixed maximum dimension or sampled constants replace these universal statements.

## Actual local checks and remaining gates

`lake build Solution` passed with **2157 graph jobs and no warnings**; the current log is `verification/proof-build.log`. The earlier unused-binder warning and its earlier log are retained separately; the current cleanup changes no mathematical proposition.

`python3 verification/fresh_check.py` separately re-elaborated Definitions, Semantics, Doubling, Growth, Proof, Solution, the isolated Challenge and an actual declaration inspection into a newly created target prefix. The old project output directory is excluded from `LEAN_PATH`. All eight commands exited zero; only Challenge has its seven deliberate placeholder warnings. All 14 implementation/public `#assert_trust kernel` and transitive-axiom reports passed with exactly `propext`, `Classical.choice`, and `Quot.sound`. No custom axiom, native proof or Challenge import occurs in the implementation.

LeanCert is used for actual explicit kernel trust auditing of this exact algebraic/counting proof. There is no numerical interval certificate, interval subdivision or root approximation to claim. All ten dependency Git trees are clean and equal the pinned manifest; these macOS checks reuse the matching compiled dependency cache and do not claim a full Mathlib source rebuild or Linux execution.

`verification/InspectProof.lean` checks the actual consumed counting/factorial/real-power dependencies and all substantive proof stages; its output is retained. The fresh driver verifies unchanged sources before and after and the seven complete source signatures with the disclosed alpha-renaming. The real independent-environment Comparator run is still a required future gate. Both independent final referees should audit the source/proof fidelity, cardinality and asymptotic quantifiers, fresh kernel acceptance and permitted axioms before Linux packaging.

| Key file | SHA256 |
| --- | --- |
| `NLA/FR12/Definitions.lean` | `0c074289e7ee518876a36caf33f1b66a286ca46e7e520c083d07b9133779bf9c` |
| `Challenge.lean` | `b7610d4a0b7416737dc9fdb3cbc24f7c154fe27bfd6b25986b7ed7b80dee28a7` |
| `NUMERICAL_TARGETS.md` | `bedc45de378f2e7429e7214f572f466e9c806abb7f02ab9921aa50f6368c9da0` |
| `NLA/FR12/Semantics.lean` | `6cba3023ab9f319ac4622a81c4bb7b0cca34da96933fc8e0507f31f6671341e7` |
| `NLA/FR12/Doubling.lean` | `841cf24ebad19caf9fe6807a67079931b5bf2fafba01d19ca256bf4f393a081e` |
| `NLA/FR12/Growth.lean` | `654930878291656c7f08fb285019d0033bc4c3e5ceebfac625ce676ce228fbaf` |
| `NLA/FR12/Proof.lean` | `a75ef4a3567d641df84f7971c4d3f182b1ae73fb87cb70d474feda5c7af69df3` |
| `Solution.lean` | `c37bbf5bb1bab85816f6c343eb3ee7bbfdadec2f6ad4dc17d11348a041ab598a` |
| `comparator.json` | `03d4d4ef6190299ee767f9c677c40d23bda8576ae35a6628fa022a0a679c1581` |
| `lakefile.toml` | `b64736762c8980abbc71aa5a7dc5f34e502ec228cdb9773673d85662d8d318c7` |
| `lake-manifest.json` | `ef45e8c3dc558df93024d94b81f42ace998ddfacc8b7948905a4b90c548742cb` |

The actual dependency traversal visits 49 project declarations and requires 20 material mathematical dependencies. The full fresh-command, source-identity, axiom, pin and dependency logs are in `verification/`, all bound by the proof freeze.
