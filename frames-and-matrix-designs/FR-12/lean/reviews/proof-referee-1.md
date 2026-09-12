# FR-12 independent final proof referee 1 — 2026-09-12

**APPROVE the complete seven-export Lean proof at the frozen hashes below.** I found no mathematical correction to request. This approval covers the full negative answer to the canonical labeled Hadamard counting conjecture and the advertised auxiliary results. Actual sandboxed Linux Comparator/default-kernel verification and its operational audit remain separate, pending gates. This is an independent AI-agent review, not external human peer review or an official Tau Ceti endorsement.

Reviewer: OpenAI Codex agent `/root/formal_review_standards`, independent of proof author `/root`. I also performed statement referee 1; both independent statement approvals preceded implementation. I did not write or edit any mathematical candidate, configuration, original source, frozen record or earlier review during this final audit.

## Exact reviewed inputs and independent execution

The complete proof freeze is `reviews/proof-freeze.json`, SHA256 `c65d4deaa3e02af8c20a584dd81b944dbdc72f262e326630e115e5fc9070aa87`. All **74 project files and four original sources** matched before and after my checks. The original statement freeze remains `5fbbcbce16da324a186dd765d120c883e4800efe2e491fbf069c9f7c74f5372c`; its two approved reports are unchanged.

| Input | SHA256 |
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

My own [fresh driver](proof-referee-1-evidence/check.py) re-elaborated Definitions, Semantics, Doubling, Growth, Proof, Solution, the isolated Challenge and my own inspection module. It used a new artifact prefix and excluded the old project build directory from `LEAN_PATH`; Challenge's output was placed in a separate prefix that the proof never imports. **All eight commands exited zero.** Only Challenge emitted its seven deliberate placeholder warnings. The actual proof modules and inspection emitted none.

All ten dependency repositories are clean and match their manifest revisions: Lean 4.33.1, LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` are recorded with the complete transitive pins. These are fresh macOS source checks with matching compiled dependency reuse, not a full Mathlib source rebuild, Linux execution or a new Comparator result.

## Full target and actual counting semantics

I read the complete canonical README, original Markdown and TeX proof, retained informal review, frozen definitions, Challenge, numerical targets, source map and every implementation module. The formal target is the original count of individual labeled real sign matrices satisfying the actual equation `A * A.transpose = n • 1`. It contains no normalization, quotient by signs or permutations, selected-family count or assumed finiteness.

This last issue is substantive because Mathlib's `Nat.card` is zero for an infinite type. The new `finiteHadamardMatrices` instance proves the actual subtype finite by an injective Boolean-entry encoding, for every dimension, including zero. The positive-dimension bridge to the actual Mathlib `Matrix.IsHadamard` proves its sign/unitary condition and derives the second Gram identity from the one-sided identity and nonzero real dimension. These are conclusions, not extra hypotheses. The finite-codomain requirement of `Nat.card_le_card_of_injective` is genuinely discharged by that instance.

The complete `CountingConjecture` retains arbitrary positive **real** `C`, every positive natural dimension divisible by four, ordinary real division in `Real.log n / Real.log 2`, and genuine real outer exponentiation. My fully explicit inspection confirms actual matrix multiplication, scalar identity, `Nat.card`, real logarithms and the `Real × Real` outer power instance. The seven normalized source signatures match Challenge exactly, apart from the unused local binder's alpha-renaming `hn` to `_hn` in `counting_semantics`. The positive-dimension premise remains present. Actual independent-environment declaration comparison still belongs to the future Comparator gate.

## Injection, recurrence and universal growth

The implemented four blocks are exactly `A`, `B`, the rows of `A` permuted by `σ`, and the negative rows of `B` permuted by the same `σ`. The four entry lemmas prove this through the real `finSumFinEquiv` reindexing. Sign membership and all four row-product cases are proved for arbitrary independent Hadamard inputs; there is no missing cross-orthogonality or commutation assumption.

Top-left and top-right entries recover the full labeled `A` and `B`. The actual Gram identity proves distinct rows of `A` are distinct vectors at positive order. Bottom-left entries therefore recover every `σ(i)`. The explicit subtype injection and the actual product/permutation cardinality theorems yield `m! H(m)^2 ≤ H(2m)` for every `m ≥ 1`, including orders with empty input sets. No collision multiplicity or automorphism-group estimate is assumed.

This is the approved smaller family of top-to-bottom matchings. It does **not** formalize the source's stronger `(2m−1)!!` recurrence. The smaller factorial factor is enough for the exact quantitative theorem and full original negation, so excluding that auxiliary source claim does not weaken the advertised target.

An actual order-one matrix establishes the positive starting count. The established recurrence then proves `1 ≤ H(2^k)` for every natural `k`. Mathlib's finite factorial inequality proves `r^r ≤ (2r)!` without asymptotic estimates. Its application at `r=2^(k+1)` and the real/natural power bridges give the exact factorial exponent used in the induction.

The proof directly inducts on the real exponential lower bound, avoiding logarithms of the count. It justifies every nonnegative product and square before multiplying inequalities. With `q=2^(k+1)>0`, the exponent identity reduces to

```math
(k+1)+2\frac{k(k+1)}4=\frac{(k+1)(k+2)}2.
```

The base case `k=0` is covered by the proved positive count. Thus `power_two_lower_bound` is exactly the manuscript bound at `K=k+2`, for every `K≥2`. The inner exponent `k+2` is natural; the outer exponent is real. The completed Solution comment correctly explains this distinction while the frozen Challenge is preserved.

For any positive real `C`, actual Archimedean choice supplies natural `k>16C+2`. Setting `d=k−16C−2>0` gives the exact strict gap

```math
\frac{k(k+1)}8-C(k+2)
=16C^2+6C+3Cd+\frac{d^2+5d+6}{8}>0.
```

The proof establishes this universally with real arithmetic, proves `log₂(2^(k+2))=k+2` using nonzero `log 2`, and invokes strict monotonicity of the genuine real power. The final theorem proves its witness dimension positive and divisible by four before contradicting the original universal bound. There is no finite range for dimensions or constants, no finite-sample extrapolation, and no omitted existence premise.

My separate [rational polynomial diagnostic](proof-referee-1-evidence/algebra_check.py) confirms both generic exponent identities coefficient-by-coefficient and the small factorial boundary cases `r=0,…,12`. It imports no author checker and performs no large matrix enumeration. These are supplementary transcription checks; the actual universal Lean proof supplies the mathematical guarantee.

## Kernel trust, reuse and review standards

The actual 14 internal/public `#assert_trust kernel` commands ran. My inspection independently reran all seven public assertions and `#print axioms` commands. All 21 printed theorem reports contain exactly `propext`, `Classical.choice` and `Quot.sound`. A separate traversal of both declaration types and proof bodies visited all **49 reached project declarations**, rejecting any transitive axiom outside that whitelist. It also required **20 actual consumed dependencies**, including the finite encoding, Hadamard bridge, injective cardinality comparison, permutation count, factorial bound, real-power identities, Archimedean choice and every material project proof stage. The selected imports are used by the proof, rather than merely listed as evidence.

I inspected the pinned LeanCert trust command: it collects transitive axioms and rejects `sorryAx`, native/compiler axioms and unknown custom axioms in kernel mode. Proof and Solution explicitly choose kernel trust. Here LeanCert provides **actual kernel trust auditing**; there is no numerical certificate to claim or interval subdivision to optimize. The symbolic construction, exact cardinality APIs and direct exponential induction avoid enumeration and unnecessary analytic computation. No implementation imports Challenge or contains `sorry`, `admit`, custom `axiom` declarations or `native_decide`.

I applied the relevant [Tau Ceti rubrics](https://github.com/TauCetiProject/TauCetiReview/tree/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/rubrics) for correctness/fidelity, scope, generality, proof quality, reuse, API design, placement, naming, documentation and attribution. The namespace and module separation are appropriate for this self-contained formalization. The genuinely generic row, block, counting and factorial lemmas support the advertised result without gratuitous new abstractions. The direct induction is a justified simplification of the informal proof. No additional library refactor or generalization is required for this project.

Mathematical proof and formalization credit remain George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with substantial AI assistance disclosed. Ferber, Jain and Zhao retain conjecture and published-upper-bound credit. No George email is added. The review does not certify historical priority, Hadamard existence at all admissible orders or a matching upper bound.

## Publication gate and retained evidence

**No mathematical changes requested.** The already disclosed current project README remains a frozen statement-stage document; it must be archived and refreshed during candidate packaging. A truthful `formalization.yaml` is not yet present and is also a packaging requirement. The historical numerical target and freeze records should remain unchanged. These documentation tasks do not overturn the proof approval, and do not justify describing Linux Comparator as completed before its actual run.

The [evidence manifest](proof-referee-1-evidence/EVIDENCE-MANIFEST.json), SHA256 `521d42c777aedcfe9a54a2a5eb5a22aea181a23bc66826a551b70b033f61afb5`, binds 23 files including my source/checker, all raw logs, exact source and pin checks, library/rubric hashes and supplementary algebra. The [fresh-check record](proof-referee-1-evidence/fresh-checks.json) is SHA256 `6353de5d8975ccb668aafe59e7188fe404ca1cb18152325a52aee36aa41c7ef2`; the [inspection](proof-referee-1-evidence/Inspect.log) is `85f53f66d949fe6f3004356d1b16ba121a8b20c6f189d6d917526f102ba32c5e`; the [axiom audit](proof-referee-1-evidence/axiom-audit.json) is `63743e7a2c4a560d3fc47f209eecdf054b0072a5a11ae702bfb5862b78f1b121`.

This referee made no canonical status, commit, push or PR change. The other independent final referee and actual Linux verification remain the parent's separately recorded gates.
