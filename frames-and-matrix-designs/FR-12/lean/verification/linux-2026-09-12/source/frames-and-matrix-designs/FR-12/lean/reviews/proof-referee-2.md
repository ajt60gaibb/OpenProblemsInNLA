# FR-12 independent final proof referee 2

**Verdict: APPROVE.** The completed Lean implementation proves all seven independently approved exports, including the complete negation of the original labeled real Hadamard counting conjecture. No mathematical correction is requested. Actual Linux Comparator and default-kernel replay remain separate pending gates; this report does not authorize a status promotion by itself.

Reviewer: independent agent `/root/leancert_examples`, 12 September 2026. I reviewed the statement package earlier but did not author or modify the implementation. I read the complete current definitions, Challenge, five implementation modules, Solution, original canonical statement and complete informal solution. This is an independent AI-agent review, not human peer review, an official Tau Ceti review, or historical-priority certification.

## Exact version and evidence

The reviewed [proof freeze](proof-freeze.json) has SHA256 `c65d4deaa3e02af8c20a584dd81b944dbdc72f262e326630e115e5fc9070aa87`; the [author handoff](proof-completion.md) has SHA256 `56bf908a87f234581dd2d93e0f975d17b95f1fddce81ba01b5e6821902474666`. I independently checked every one of the freeze's **74 project files and four original sources** before and after the checks. All remain unchanged, as do all 19 original statement inputs.

| File | SHA256 |
| --- | --- |
| `NLA/FR12/Definitions.lean` | `0c074289e7ee518876a36caf33f1b66a286ca46e7e520c083d07b9133779bf9c` |
| `Challenge.lean` | `b7610d4a0b7416737dc9fdb3cbc24f7c154fe27bfd6b25986b7ed7b80dee28a7` |
| `NUMERICAL_TARGETS.md` | `bedc45de378f2e7429e7214f572f466e9c806abb7f02ab9921aa50f6368c9da0` |
| `NLA/FR12/Semantics.lean` | `6cba3023ab9f319ac4622a81c4bb7b0cca34da96933fc8e0507f31f6671341e7` |
| `NLA/FR12/Doubling.lean` | `841cf24ebad19caf9fe6807a67079931b5bf2fafba01d19ca256bf4f393a081e` |
| `NLA/FR12/Growth.lean` | `654930878291656c7f08fb285019d0033bc4c3e5ceebfac625ce676ce228fbaf` |
| `NLA/FR12/Proof.lean` | `a75ef4a3567d641df84f7971c4d3f182b1ae73fb87cb70d474feda5c7af69df3` |
| `Solution.lean` | `c37bbf5bb1bab85816f6c343eb3ee7bbfdadec2f6ad4dc17d11348a041ab598a` |

My separate [evidence manifest](../verification/final-referee-2/evidence-manifest.json) binds 19 independent evidence files and has SHA256 `35d982e54b27b0fecb65bcecd05f0cfbc8aa5957b5398e919ff580e2b3f46b09`. The [fresh command record](../verification/final-referee-2/fresh-checks.json) has SHA256 `fe2403ae696f245599a87fc1befce1ad278d4f91bdf5d40368f136c4009a7cf6`. No prior reviewer or author log was substituted for these executions.

## Mathematical fidelity and adversarial checks

**Objects and quantifiers.** `Mat n` is the actual real matrix type with two labeled `Fin n` indices. `IsRealHadamard` requires every entry to be exactly ±1 and the actual Gram product to be n times the identity. `HadamardMatrices` is this matrix subtype, with no quotient or normalization. The conjecture quantifies one arbitrary positive real C and every positive natural n divisible by four, using the actual real power and `Real.log n / Real.log 2`. The final negation retains all these quantifiers.

**Finiteness and standard semantics.** The Boolean-entry encoding is injective because every entry is one of two distinct real values. This proves finiteness at every dimension; `Nat.card` cannot conceal an infinite set. The positive-dimensional equivalence to Mathlib's `Matrix.IsHadamard` uses the actual real-unitary characterization and the actual one-sided Gram theorem. Its regularity premise is discharged from n≥1. The standard predicate requires both Gram identities, and the implementation derives that condition rather than assuming it. The same normalization proves genuine row injectivity: equal distinct rows would have inner product both n>0 and zero.

**Construction and collisions.** The four block lemmas establish the actual entries after `finSumFinEquiv` reindexing. For every original pair A,B and every permutation σ, all entries remain signs. Top/top and bottom/bottom Gram entries add the two separate Gram entries; mixed entries subtract identical delta contributions. No relation between A and B is assumed. Equality of outputs recovers A from the top left block, B from the top right, then σ pointwise from the bottom left using the proved row injectivity. Thus the actual map is injective on its complete stated domain. The map is then lifted to the genuine Hadamard subtype, and `Nat.card_le_card_of_injective`, actual product cardinalities and `Fintype.card_perm` give exactly m!H(m)²≤H(2m). All finiteness obligations are supplied. Orders with no inputs cause no hidden existence premise.

This restricted top/bottom matching family has only m! choices. The source's stronger all-matching factor is explicitly outside these exports. The restricted construction nevertheless proves the same displayed growth bound and the full original negation; it does not substitute an easier counting problem.

**Universal growth and casts.** An actual order-one matrix starts the positivity induction. The factorial estimate r^r≤(2r)! follows from the exact natural factorial-product inequality and r!≥1. At r=2^(k+1), the proof carefully converts natural powers and casts to the required real exponential factorial bound. Squaring the induction bound is legitimate because its left side is nonnegative. With d=2^(k+1), the next exponent identity reduces to

```math
d(k+1)+2\frac{2d\,k(k+1)}8
=\frac{4d(k+1)(k+2)}8.
```

The implementation proves this exact identity and uses the actual real-power multiplication laws, obtaining H(2^(k+2))≥2^(2^(k+2)k(k+1)/8) for every k≥0. This is precisely the source's index-shifted bound. The inner exponent k+2 is natural; the outer exponent is real. No logarithm of an unknown count or approximate factorial estimate is needed.

**Every constant is excluded.** The true logarithm identity at the selected powers of two is proved with log 2>0. For any C>0, Archimedean choice supplies a natural k>16C+2. Independently, k>2 gives k+2≤2k, while k>16C yields 2Ck<k²/8<k(k+1)/8. This establishes the strict exponent gap used by the implementation's exact polynomial proof. Strict monotonicity of 2^x gives an actual count larger than the proposed upper bound. The final theorem proves that the selected n is positive and divisible by four before applying the alleged universal bound. No finite sample, bounded range of C, assumed recurrence, assumed injectivity, or assumed growth theorem replaces this argument.

## Independent compilation, trust and proof quality

I executed [my own fresh driver](../verification/final-referee-2/fresh_check.py), with a newly created output prefix and the original project build directory removed from `LEAN_PATH`. Definitions, Semantics, Doubling, Growth, Proof, Solution, isolated Challenge and [my declaration inspector](../verification/final-referee-2/Inspect.lean) all exited zero. Only Challenge produced its seven deliberate placeholder warnings; it is not imported into the implementation. Matching compiled dependency artifacts were reused on macOS, not rebuilt from all Mathlib sources.

The 14 implementation/public and seven independent `#assert_trust kernel` checks passed. All **21 actual transitive axiom reports** contain exactly `propext`, `Classical.choice`, and `Quot.sound`. I inspected LeanCert's pinned `collectAxioms`-based command: its kernel mode rejects native-compiler, sorry and custom axioms. There is no interval certificate in this exact proof, and none is claimed or mathematically needed.

My inspector traversed **49 actual project declarations** and required **25 consumed mathematical dependencies**, including the finite matrix encoding, standard Hadamard bridge, actual injection and cardinality lemmas, initial nonempty count, factorial growth, logarithm identity, strict real-power comparison and final contradiction. I read the complete inspection output. All seven complete source signatures match Challenge after the sole disclosed unused-binder alpha-renaming `hn` to `_hn`. This source comparison is not a substitute for the later independent-environment Comparator run.

All ten dependency checkouts are clean at their manifest commits, including Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. The fresh compiler is Lean 4.33.1. Exact library and rubric source hashes are retained in [the source audit](../verification/final-referee-2/library-and-rubric-sources.json).

I applied the relevant correctness, scope, proof-quality and attribution criteria from Tau Ceti Review at `afb424eda89e8ac96d9eb69f6a88972055a4cd1b`, adapted to this one NLA target rather than Tau Ceti's unrelated roadmap. The factored proofs expose the substantive constructions and cast bridges; routine automation discharges exact finite algebra. George Stepaniants retains proof/formalization credit with the approved Caltech department affiliation, Ferber–Jain–Zhao retain the conjecture and prior-bound attribution, and AI assistance is disclosed. No email was added.

**Nonblocking packaging note.** The frozen statement-stage README and numerical-plan status are historical. Candidate publication must clearly label or archive that stage and give the current proof/review status without altering the frozen mathematical boundary. The author already disclosed this item. Preserve the distinction between the formally proved m! recurrence and the stronger informal all-matching recurrence. No mathematical file was edited during this review, and no commit, push, PR or canonical status change was performed.
