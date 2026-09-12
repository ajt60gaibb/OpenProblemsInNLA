# FR-12 Lean formalization

The complete original labeled real Hadamard counting conjecture is refuted by
the implemented proof. All seven exports passed local Lean checks, two
independent statement reviews and two independent final proof reviews.
**Actual Linux Comparator, separate default-kernel replay and their operational
audit are pending.** The canonical status remains **Solved**.

**Mathematical proof and formalization:** George Stepaniants, Department of
Computing and Mathematical Sciences, California Institute of Technology,
Pasadena, California, USA, with substantial AI-agent assistance.
Ferber, Jain and Zhao retain the original conjecture and published-upper-bound
credit. Independent AI-agent reviews are not external human peer review,
official Tau Ceti endorsement or historical-priority certification.

## Complete original target

For each positive integer `n`, `H(n)` counts individual labeled real sign
matrices satisfying the actual Gram identity `A * A.transpose = n • 1`.
There is no quotient by signed permutations or normalization of the matrices.
The full assertion asks for a single positive real `C` such that

```math
H(n)\leq 2^{C n\log_2 n}
```

for every positive natural `n` divisible by four. [Definitions](NLA/FR12/Definitions.lean)
use this exact subtype, actual `Nat.card`, genuine real exponentiation and
`Real.log n / Real.log 2`. The proof establishes that the subtype is finite in
every dimension; it does not assume finiteness to conceal an infinite count.
At every positive dimension it also proves equivalence to Mathlib's actual
`Matrix.IsHadamard` predicate.

The complete [canonical target](../README.md) and George's
[informal proof](../solution.md) are retained at source revision
`8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`. See the unchanged
[numerical targets](NUMERICAL_TARGETS.md) and [source map](SOURCE_MAP.md).
Their statement-stage labels record the original approved boundary; this guide
describes the current proof/review status.

## Exact proof and advertised exports

For arbitrary order-`m` Hadamard matrices `A`, `B` and a permutation `σ`, the
actual construction has top rows `(A_i,B_i)` and bottom rows
`(A_(σ i),-B_(σ i))`. The top halves recover both original labeled matrices;
the bottom first half and proved row injectivity recover the permutation.
Every output is Hadamard. Counting this actual injection proves

```math
m!\,H(m)^2\leq H(2m)\qquad(m\geq1).
```

**The formally proved recurrence has factor `m!`.** The source's stronger
all-perfect-matching factor `(2m−1)!!` is outside these exports. The smaller
family already proves the exact source lower bound and the full canonical
negation, with no restriction on the count or conjecture being refuted.

[Semantics](NLA/FR12/Semantics.lean) proves finite counting and genuine row
orthogonality. [Doubling](NLA/FR12/Doubling.lean) proves the block entries,
Hadamard property, injectivity and cardinality comparison.
[Growth](NLA/FR12/Growth.lean) begins with an actual order-one matrix and
derives positivity at every power of two, an exact factorial bound and

```math
H(2^{k+2})\geq2^{\,2^{k+2}k(k+1)/8}\qquad(k\in\mathbb N).
```

This is exactly the source bound at `K=k+2`. The inner exponent `k+2` is
natural; the outer exponent is real. Direct induction on the exponential
inequality avoids logarithms of the count and asymptotic factorial estimates.
For every positive real `C`, Archimedean choice supplies `k>16C+2`; the proved
strict exponent gap and the actual base-two logarithm identity give a positive
multiple-of-four order violating that `C`'s proposed bound.

The [frozen Challenge](Challenge.lean) and [completed Solution](Solution.lean)
have these seven declarations, each with prefix `NLA.FR12.`:

| Declaration | Complete scope |
| --- | --- |
| `counting_semantics` | Actual finite matrix count in every dimension and equivalence to Mathlib Hadamard matrices in positive dimension. |
| `injective_doubling` | Every output of the concrete map is Hadamard and the map is injective for all `m≥1`. |
| `factorial_doubling` | The actual cardinalities satisfy `m! H(m)²≤H(2m)` for all `m≥1`. |
| `power_two_nonempty` | A positive count at every order `2^k`, including order one. |
| `power_two_lower_bound` | The displayed exact quantitative bound for every natural `k`. |
| `counterexample` | Every positive real constant fails strictly at a power-of-two multiple of four. |
| `not_countingConjecture` | Unconditional negation of the complete original counting assertion. |

The formalization does not claim the stronger matching recurrence, Hadamard
existence at every admissible order, a matching upper bound or historical
priority. The only source-signature difference is the harmless alpha-renaming
of the unused bound variable `hn` to `_hn` in `counting_semantics`; its original
positive-dimension premise remains intact. Challenge is byte-identical.

## Kernel trust and independent reviews

The pins are Lean **4.33.1**, [LeanCert 621a43d](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926)
and [Mathlib 0df444a](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474).
Proof and Solution explicitly select `leancert.trust "kernel"`.
**LeanCert performs actual kernel trust auditing of this exact proof. There is
no numerical interval certificate, root approximation or interval subdivision.**
The symbolic injection and direct exponential induction avoid large matrix,
matching or integer enumeration in Lean.

All fourteen internal/public source `#assert_trust kernel` checks and their
transitive axiom reports pass with exactly `propext`, `Classical.choice` and
`Quot.sound`. Each independent final referee freshly reran the source modules
and seven additional public kernel assertions. Both traversed all 49 reached
project declarations and confirmed the actual material mathematical dependencies.
There are no proof-development or definition holes, custom axioms or native
proofs. Solution does not import Challenge. The seven intentional Challenge
placeholders are isolated and excluded from proof-development sorry counts.

- Statement approvals before implementation: [referee 1](reviews/statement-referee-1.md)
  and [referee 2](reviews/statement-referee-2.md).
- Independent final approvals: [referee 1](reviews/proof-referee-1.md)
  and [referee 2](reviews/proof-referee-2.md).
- [Proof-start record](verification/proof-start.json),
  [complete proof freeze](reviews/proof-freeze.json) and
  [author handoff](reviews/proof-completion.md).
- Independent raw evidence: [referee 1](reviews/proof-referee-1-evidence/EVIDENCE-MANIFEST.json)
  and [referee 2](verification/final-referee-2/evidence-manifest.json).
- [v0.4 manifest](formalization.yaml), [Comparator configuration](comparator.json),
  [dependency pins](lake-manifest.json) and
  [candidate preservation evidence](verification/linux-candidate-2026-09-12/).

The author's 2157-job build and the independent fresh-source checks are local
macOS runs with matching compiled dependency reuse at ten clean pinned Git
revisions. They do not claim all Mathlib dependencies were rebuilt from source
or that the Linux verifier ran. The relevant
[pinned Tau Ceti standards](../../../docs/lean/REVIEW.md) were applied within
the scope of this complete original target.

## Reproduction and pending Linux gate

From this directory with its exact toolchain and manifest:

```
lake exe cache get
lake build Solution
lake env lean Solution.lean
```

After the candidate has an immutable Git revision, use the repository's
[shared workflow](../../../docs/lean/README.md) on a correctly configured
[non-root Linux host](../../../tools/lean/HARNESS.md). From the repository root:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  frames-and-matrix-designs/FR-12/lean \
  /absolute/path/to/nla-lean-tools
```

The actual run must build/export the independently checked Challenge and
Solution, compare all seven declarations with no definition exceptions, replay
the proof through Lean's default kernel, and pass the real isolation and
rejection controls. [Comparator](comparator.json) permits only the three
standard axioms. No FR-12 Linux run or operational PASS is claimed yet.

The exact historical README is archived at
[the frozen statement-stage copy](verification/linux-candidate-2026-09-12/frozen-statement-stage-README.md).
Only this current README changes among the 74 proof-freeze inputs; the other
73, all four original sources, all mathematical statements/proofs, pins,
configuration and both statement/final review reports remain unchanged.
The current manifest and candidate records describe completed local gates and
pending Linux verification. Canonical status remains Solved until actual
verification evidence receives its separate operational and publication review.
