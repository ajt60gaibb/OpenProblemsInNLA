# FR-12 independent statement referee 2

**Decision: APPROVE the frozen statement boundary.** No mathematical correction is
requested. This is a statement review, not approval of a completed Lean proof or
a claim that Linux Comparator has run. The seven intentional Challenge
placeholders remain. Proof work requires the other independent statement
approval as well.

Reviewer: Codex agent `/root/leancert_examples`, independent of the statement
author `/root`. Date: 12 September 2026. The review applies the Tau Ceti
correctness, definition-fidelity, scope, reuse, and attribution criteria as
appropriate to this project; it is not an official Tau Ceti or human review.

## Frozen inputs

The reviewed freeze is
`reviews/statement-freeze.json`, SHA256
`5fbbcbce16da324a186dd765d120c883e4800efe2e491fbf069c9f7c74f5372c`.
All 19 project inputs and four original-source inputs matched before and after
the independent checks. No frozen file was edited. Key hashes are:

| Input | SHA256 |
| --- | --- |
| `NLA/FR12/Definitions.lean` | `0c074289e7ee518876a36caf33f1b66a286ca46e7e520c083d07b9133779bf9c` |
| `Challenge.lean` | `b7610d4a0b7416737dc9fdb3cbc24f7c154fe27bfd6b25986b7ed7b80dee28a7` |
| `NUMERICAL_TARGETS.md` | `bedc45de378f2e7429e7214f572f466e9c806abb7f02ab9921aa50f6368c9da0` |
| `SOURCE_MAP.md` | `b51b279533e68cdb4fc4e329ad7134d0b967e187df955d78291b8e3e0c62898c` |
| `comparator.json` | `03d4d4ef6190299ee767f9c677c40d23bda8576ae35a6628fa022a0a679c1581` |
| Original canonical README | `7dd5ff967994bd43b3d9525b4cd9c89622962e1aa502ed681c8afb6d48011af3` |
| Complete original `solution.md` | `60ffef5d41d8986df21d25bc539f8761c86a5d64c43bb1012f110ed9917e4d59` |
| Complete original `solution.tex` | `700b2190651608a68c1449c065f318902180d1cc634e8845ea51d3ee5a57c163` |
| Original informal `REVIEW.md` | `306dfae7a7d2ebe87f27ee3851b62baf8b1a4b0193d344de5eb18d226f652963` |

The complete local statement, manuscript, source map, numerical plan, and
historical review were read. The relevant definition and Conjecture 1.3 on
pages 455–456 of the published Ferber–Jain–Zhao paper were separately checked:
the count is of distinct labeled sign matrices with orthogonal rows, and the
conjecture is an upper bound of order `2^(C n log n)` over positive multiples of
four. The row-permutation discussion also confirms that equivalence classes
are not being counted. [Published primary source](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/887EFBBF79B804BCDD942029283D4CD7/S0963548321000377a.pdf/on_the_number_of_hadamard_matrices_via_anticoncentration.pdf).

## Meaning of the complete target

`IsRealHadamard` uses actual `Matrix (Fin n) (Fin n) ℝ`, entrywise membership in
`{1,-1}`, actual matrix multiplication and transpose, and `AAᵀ = nI`.
`HadamardMatrices` is the subtype of those actual arrays. It does not quotient
labels, signs, or permutations. `hadamardCount` is its actual `Nat.card`.

I checked the pinned definitions of `Nat.card` and `Matrix.IsHadamard`.
`Nat.card` would return zero on an infinite type, but the first required export
unconditionally proves finiteness for every dimension. No finiteness assumption
is smuggled into the conjecture. The same export must prove equivalence to
Mathlib's actual Hadamard notion at every positive dimension. Over the reals,
the pinned unitary-entry characterization is precisely `1` or `-1`; star is
trivial. The available `Matrix.IsHadamard.of_mul_conjTranspose` requires the
nonzero dimension scalar and supplies the reverse Gram identity. Thus the
requested bridge is meaningful and matches the original one-sided definition.

`CountingConjecture` retains an arbitrary positive real constant, every positive
natural dimension divisible by four, the actual count, actual real logarithm
quotient `Real.log n / Real.log 2`, and real outer exponentiation. No numerical
cutoff, arithmetic-progression restriction beyond the source, or strengthened
premise weakens the target. The auxiliary zero-dimensional definition does not
alter the positive-dimensional conjecture.

## Construction and every required export

The seven Challenge signatures are appropriate, complete proof obligations:

1. Finiteness and agreement with actual Mathlib Hadamard matrices, as above.
2. Every output of the concrete doubling map is Hadamard, and the map is
   injective for arbitrary positive `m`. Neither property is an assumption.
3. The unconditional exact recurrence `m! H(m)^2 ≤ H(2m)`.
4. Nonemptiness at every power-of-two order, including order one.
5. The manuscript's exact lower bound, with the harmless shift `K = k+2`.
6. Failure of the proposed bound for every positive real constant, with an
   actual power-of-two witness and actual base-two logarithm.
7. Unconditional negation of the complete original conjecture.

I inspected `Matrix.fromBlocks`, `Matrix.reindex`, `finSumFinEquiv`, and the
fully explicit elaborated application. The concrete matrix has top rows
`(A_i, B_i)` and bottom rows `(A_(σ i), -B_(σ i))`. Reindexing is a bijection to
the original `Fin (m+m)` labels; it is not a quotient. Arbitrary independent
Hadamard matrices `A` and `B` suffice for all row products. No commutation or
cross-orthogonality `ABᵀ=0` is required.

Top blocks recover both inputs. At positive order, the rows of `A` are
distinct: equality of two rows would make the off-diagonal Gram entry equal
to `m`, contradicting its value zero. The lower-left block therefore recovers
the permutation. This justifies the full-domain injectivity obligation, with
no assumed automorphism-group cardinality. Applying finite cardinality to the
actual codomain and the full product domain gives the stated factorial factor.

This is a restriction of the source construction to matchings between the
first and second blocks of labels. The matching pairs top label `j` with
bottom label `σ⁻¹ j`. There are exactly `m!` such permutations. It is legitimate
to omit the stronger all-matchings recurrence `(2m-1)!! H(m)^2`: the smaller
factor still gives the same exported lower bound and full conjecture negation.
The omission is disclosed in the statement and numerical plan.

The required universal inference is valid. For `m = 2r`, `r ≥ 1`, the exact
factorial bound `(2r)! ≥ r^r` yields the source normalized-log increment
`(K-2)/4`; summing gives `2^K(K-1)(K-2)/8`. The shifted export is precisely this
formula at `K=k+2`, including `k=0`. Nonempty power-of-two matrix sets must be
proved before any logarithm of a count is used. The actual casts, natural
powers, real powers, and `log₂(2^(k+2)) = k+2` remain proof obligations.

For any real `C>0`, choose a natural `k>16C+2`. Then `k≥2` and
`C(k+2) ≤ 2Ck < k²/8 < k(k+1)/8`. Archimedean existence and strict monotonicity
of the actual real power give strict failure. The corresponding order is
positive and divisible by four. This is a universal mathematical argument;
finite diagnostics are not being used as an asymptotic proof.

## Independent execution and diagnostics

My separate driver `statement-referee-2-evidence/fresh_check.py` completed with
exit 0. It uses Lean 4.33.1 in a new `.verification` artifact prefix, explicitly
removes the old project build path from `LEAN_PATH`, and re-elaborates
Definitions, Challenge, and my own `Inspect.lean` in dependency order. All three
commands passed. Definitions and inspection have no warnings; Challenge has
exactly the seven intentional `sorry` warnings. No Proof or Solution source
was present before or after the checks.

The fully explicit inspection confirms the meanings described above and checks
all seven exported signatures. Six actual LeanCert kernel trust assertions and
six corresponding `#print axioms` commands on the definitions passed, each with
exactly `propext`, `Classical.choice`, and `Quot.sound`. Those are audits of
definitions, not of the seven unimplemented theorems. All ten dependency Git
trees are clean and match the frozen manifest pins, including Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`.

My independent exact-integer diagnostic script does not import the author's
checker. It enumerates `H(1)=2` and `H(2)=8`, obtains 4 and 128 distinct valid
restricted-construction outputs respectively, and recovers every input triple.
With a deliberately restricted pair of order-four input matrices and every
permutation, it obtains 96 distinct valid outputs and recovers all inputs. The
latter is not a full enumeration of order-four Hadamard matrices. Exact
integer/eighth-power checks verify the recurrence-derived bound through
`K=10`; exact rational checks confirm the index shift and several sample
constant gaps. These checks supplement the universal reasoning only.

The actual source, outputs, pins, input identities, and supplementary
reconstruction are retained under `statement-referee-2-evidence/` and bound by
its `evidence-manifest.json`. Pinned Mathlib and LeanCert files inspected are
listed by hash in `library-source-hashes.json`. These fresh macOS checks reuse
pinned dependency artifacts; they do not claim a source rebuild of Mathlib,
Linux sandbox verification, or a completed Comparator run.

## Trust, attribution, and nonblocking clarification

Kernel-only LeanCert trust audits are appropriate for this exact universal
algebraic/counting proof. I inspected the actual trust command: it recursively
collects axioms and rejects `sorryAx`, native-compiler trust, and custom axioms
in kernel mode. There is no numerical interval domain needing subdivision and
no reason to introduce an artificial point certificate. Any future numerical
certificate must itself use kernel trust and be consumed by the proof.

The source proof and formalization credit George Stepaniants, with the approved
Department of Computing and Mathematical Sciences, California Institute of
Technology affiliation and AI-assistance disclosure. No new personal email is
present. The manuscript's attribution to Ferber–Jain–Zhao is retained. Nothing
in the reviewed claim resolves existence at every admissible order, supplies a
matching upper bound, or certifies historical priority.

One nonblocking wording clarification is recorded without changing the frozen
bytes: the doccomment before `power_two_lower_bound` says all displayed
exponents are real. In the actual signature, the inner exponent `k+2` of the
real base is natural, and the outer exponent is real. `NUMERICAL_TARGETS.md`
already states this correctly. The mathematical signature is correct. Root
has agreed to add a precise explanatory note to the later publication README;
this does not require a statement change or re-review.

**Result:** this referee's statement gate is satisfied at the exact hashes
above. There is no mathematical correction request. Final proof review, axiom
audits of the completed exports, Linux kernel checks, and Comparator remain
separate later gates.
