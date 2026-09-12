# FR-12 independent statement referee 1

**APPROVE for the statement gate only.** The seven frozen declarations faithfully
state the complete original labeled real Hadamard counting target and sufficient
universal obligations for its negation. I found no blocking definition, quantifier,
counting, sign, power, logarithm or endpoint mismatch. This approves implementation
after the second independent statement approval; it does not approve a completed
proof or repository status promotion.

Reviewer: independent agent `/root/formal_review_standards`, 12 September 2026.
I did not author or alter the FR-12 statement package or its mathematical source.
I read the complete retained canonical README, `solution.tex`, `solution.md`,
earlier informal review, Definitions, Challenge, NUMERICAL_TARGETS and SOURCE_MAP.
I inspected the actual pinned Mathlib definitions and ran my own fresh elaboration
and independent exact reconstruction. This is an AI-agent review, not external
human peer review, Tau Ceti endorsement or historical-priority certification.

## Exact binding and checks

The reviewed `reviews/statement-freeze.json` has SHA-256
`5fbbcbce16da324a186dd765d120c883e4800efe2e491fbf069c9f7c74f5372c`.
All 19 candidate files remain unchanged. Its four original sources match both
the worktree and their Git blobs at upstream
`8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`.

| Frozen boundary | SHA-256 |
| --- | --- |
| `NLA/FR12/Definitions.lean` | `0c074289e7ee518876a36caf33f1b66a286ca46e7e520c083d07b9133779bf9c` |
| `Challenge.lean` | `b7610d4a0b7416737dc9fdb3cbc24f7c154fe27bfd6b25986b7ed7b80dee28a7` |
| `NUMERICAL_TARGETS.md` | `bedc45de378f2e7429e7214f572f466e9c806abb7f02ab9921aa50f6368c9da0` |
| `SOURCE_MAP.md` | `b51b279533e68cdb4fc4e329ad7134d0b967e187df955d78291b8e3e0c62898c` |
| `comparator.json` | `03d4d4ef6190299ee767f9c677c40d23bda8576ae35a6628fa022a0a679c1581` |

My three independent source commands re-elaborated Definitions, Challenge and a
separate inspection module into a fresh output prefix with the author's project
build directory excluded from `LEAN_PATH`. All returned zero. Definitions and
inspection emitted no warnings; Challenge emitted exactly seven intentional
placeholder warnings. All six definition-level `#assert_trust kernel` checks
passed, and their axiom reports are exactly `propext`, `Classical.choice` and
`Quot.sound`. Every Challenge theorem explicitly reports `sorryAx`, as expected
at this stage; none is represented as proved. No Proof or Solution exists.

All ten dependency repositories match the complete Lake manifest and have clean
tracked source trees. Lean is 4.33.1, LeanCert is
`621a43d7cf21f87872392a01e874f2f1dbddc926`, and Mathlib is
`0df444a360eaa60ab8c11dca51a86af692955474`. These are local macOS checks against
pinned cached dependencies, not authoritative Linux sandbox or kernel replay.
Raw commands, logs, receipts, inspection source and exact diagnostics are in
[statement-referee-1-evidence](statement-referee-1-evidence/). The result record
has SHA-256 `bca12278fd750e4f2089a1410e7a531a599104262157cc6b52f5a74f59a755c6`.

## Definition and full-target fidelity

`Mat n` is exactly a real `Fin n × Fin n` matrix. The elaborated multiplication
in `IsRealHadamard` is actual matrix multiplication, followed by ordinary
transpose; the right side is real scalar multiplication of the matrix identity.
The entry predicate explicitly permits exactly `1` and `−1`. There is no
entrywise product, normalization, arbitrary family, chosen representative or
quotient by signed permutations.

`HadamardMatrices n` is the subtype of those actual labeled matrices.
`hadamardCount` uses `Nat.card`, whose value would be zero for an infinite type.
This possible trap is addressed by the unconditional `counting_semantics` export:
it must prove the exact subtype finite for every n. Finiteness is not assumed
as an extra hypothesis. Each matrix has only two choices per labeled entry, so
an injection into the finite Boolean matrix type supplies a valid proof route.
The n=0 extension is harmless; the original conjecture only uses n≥1.

I read Mathlib's actual `Matrix.IsHadamard`: it requires unitary entries and both
Gram identities. Over the reals unitary entries are exactly signs. Its
`of_mul_conjTranspose` theorem derives the second identity when the dimension is
regular. The positive-dimension hypothesis in `counting_semantics` supplies a
nonzero real dimension, so this stronger library predicate has a legitimate
bridge. The formalization must prove that bridge; it is a conclusion here.

`CountingConjecture` quantifies an arbitrary positive **real** C, every positive
natural n divisible by four, and the canonical upper bound. Explicit-instance
inspection confirms the outer power is genuine `Real.rpow`, the exponent has
real multiplication and real division, and the logarithm is
`Real.log (n : ℝ) / Real.log 2`. Its base is exactly two and its denominator is
nonzero. No finite range, rational-only C or restriction to powers of two is
inserted into the conjecture being refuted.

## Restricted construction and cardinality

The actual `doublingMatrix` uses `Matrix.fromBlocks`, row `submatrix σ id`,
negation and a genuine reindexing equivalence. I inspected `Matrix.reindex` and
`finSumFinEquiv`: the latter maps `inl i` to label i and `inr i` to label m+i.
Consequently the four blocks are exactly A, B, A with rows permuted by σ, and
minus B with the same row permutation. Reindexing preserves every matrix label;
it does not quotient the output set.

The construction is valid for independently chosen A and B. Top/top inner
products add their two equal Kronecker-delta Gram contributions; top/bottom
products subtract those contributions and vanish; bottom/bottom products add,
with σ's injectivity preserving the delta. No relation such as A Bᵀ=0 or
commutativity is missing.

The top blocks recover the entire labeled A and B. Distinct rows of A cannot be
equal: their inner product would have to be both zero and m, contrary to m≥1.
The bottom-left row then uniquely determines σ(i). This proves the proposed
injectivity is feasible on the entire domain, including all signs and all input
row orders. For an order with no Hadamard matrix the domain is empty and the
recurrence is still true.

There are exactly m! permutations. `injective_doubling` requires validity and
injectivity as conclusions; `factorial_doubling` counts the actual matrix
subtypes and requires the smaller recurrence m! H(m)²≤H(2m). The displayed
`m+m` output dimension and `2*m` counting dimension agree arithmetically. This
restricted family is a subset of the source's perfect-matching construction and
uses precisely the factorial estimate already sufficient in its iteration.
The stronger factor `(2m−1)!!` is explicitly excluded from the formal exports.
No automorphism-group estimate is needed or assumed.

## Quantitative and asymptotic obligations

`power_two_nonempty` requires an actual positive count for every natural k,
including k=0 (order one), before any logarithm of the count is used. A concrete
order-one sign matrix and the proved doubling construction suffice.

For even m=2r, r≥1, the elementary estimate `(2r)!≥r^r` is valid. The pinned
`Nat.factorial_mul_pow_sub_le_factorial` can derive it with factorial positivity.
It does not require numerical enumeration. At order 2^K the logarithmic
increment is exactly `(K−2)/4`; summation yields the source's quadratic exponent.

`power_two_lower_bound` uses K=k+2. Its real exponent is
`2^(k+2) * k * (k+1) / 8`, exactly the source's
`2^K (K−1)(K−2)/8` for every K≥2. Inspection confirms the inner power has a natural
exponent and real base, while the outer power has a real exponent. Casting a
natural power of two gives the same inner value. No truncated natural
subtraction or natural-number division changes the coefficient. The k=0 case
correctly asks only for a count at least one.

For every C>0, an Archimedean choice of natural k with k>2 and k>16C gives
`k(k+1)/8 > C(k+2)`. This is an exact algebraic route, not a finite numerical
check. With n=2^(k+2), the actual identity `log₂ n=k+2`, positivity of n and strict
monotonicity of `2^x` convert the universal lower bound to the strict failure
exported by `counterexample`. Such n are positive multiples of four. The final
`not_countingConjecture` therefore negates the full original target without
additional assumptions. It does not claim Hadamard existence at all admissible
orders or a matching upper bound.

My independent integer checker enumerated only the input matrices at m=1,2.
It checked all 4 and 128 constructed outputs, their exact Gram identities and
recovery of every input triple. These are construction output counts, not exact
H(2) or H(4). It additionally checked the weaker recurrence and exact exponent
identity at K=2,…,12 by eighth powers of integers, and five rational C examples
for the Archimedean choice. All passed. These finite diagnostics are
supplementary; the universal statements still need Lean proofs.

## Review standards, scope and remaining gates

I applied the relevant [Tau Ceti correctness and faithfulness rubric](https://github.com/TauCetiProject/TauCetiReview/blob/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/rubrics/correctness.md)
and its scope, generality, reuse, placement, naming, documentation and attribution
angles to this **statement stage**. The generic construction and recurrence have
natural generality; the definitions are local to `NLA.FR12`; existing Mathlib
matrix, cardinality, factorial and real-analysis APIs are appropriately targeted.
There is no fake prerequisite bundled into a hypothesis. Proof quality and
absence of proof-level trust defects cannot receive final approval while the
implementation is intentionally absent.

LeanCert is genuinely pinned for explicit kernel trust auditing. This exact
combinatorial/real-analysis argument does not require an interval certificate;
adding a decorative numerical inequality would not improve its evidence. The
proposed symbolic construction avoids enumerating large matrix or matching
families. If a later interval obligation arises, it must first be stated and
minimized, then certified in kernel.

The Comparator configuration names all seven exports, has no definition-name
exceptions, and permits only the standard three axioms. A truthful manifest,
two independent final proof reviews and actual Linux isolation, negative
controls, kernel replay and Comparator verification are future requirements.
The local statements and earlier informal review do not establish those passes.

Mathematical source proof and formalization are credited to George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA, with AI assistance disclosed. Ferber,
Jain and Zhao retain conjecture and upper-bound credit. No George email is
present. The stronger source recurrence, historical priority and outside human
review are not claimed as formal results by this package.

**No source changes requested.** Both independent statement approvals remain
necessary before implementation. This report requests no canonical or Git change.
