# PR 192 / IE-23 independent mathematical and formal-target review

**Verdict: PASS for mathematical correctness, original-target fidelity, and source-level proof closure. No mathematical blocker found.** The p=4 witness refutes the entire original universal assertion and proves global minimality over all complex right inverses. This review does not authenticate Linux execution; that is being independently handled by the coordinating reviewer. No local Lean execution or new kernel replay is claimed.

Reviewed head: `3fc8bde9c014d22575bbfb73c644c5ce0c492d29`. Published comparison base: `5830ed4fb06da0659414a3deb2a40ad327aca052`. Canonical path remains `linear-systems-and-elimination/IE-23/README.md`. The complete original `## Problem statement` section and `problem_ids.json` are byte-identical to that base. Colbrook retains mathematical authorship; Stepaniants receives formalization credit; Dokmanić–Gribonval retain original-example/question credit. I read the unchanged canonical statement and the source manuscript's actual theorem and proof, not only the submitted correspondence/PASS reports.

## Complete proof closure reviewed

Read `Definitions.lean`, `Norms.lean`, `Matrices.lean`, `FourthPower.lean`, `Actions.lean`, `Minimizers.lean`, `Proof.lean`, and `Solution.lean` completely, together with the eight Challenge declarations, comparator, project configuration, manifest and toolchain. The only non-Mathlib imported project code is this full mathematical chain and LeanCert's trust inspection module. Challenge is excluded from the Solution closure. All eight public Solution signatures match Challenge after whitespace normalization. The comparator has no definition exceptions and permits only `propext`, `Classical.choice`, `Quot.sound`.

A comment-stripped scan of all project mathematical modules and Solution found no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, `run_tac`, custom `elab`, `macro`, or `syntax`. The eight intentional Challenge placeholders remain isolated. Source review is not a substitute for the separately authenticated transitive-axiom and kernel results.

## The full original proposition and actual supremum

The formal conjecture keeps independent natural dimensions `1 ≤ m < n`, all complex `m × n` matrices with actual `Matrix.rank A = m`, every real `p > 2` (therefore finite), and every distinct complex right inverse. The objective is directly `X.mulVec y`, not the separate `X*A` product norm. The pseudoinverse uses the canonical actual formula `A.conjTranspose * (A * A.conjTranspose)⁻¹`, without replacing the inverse by a proposed rational matrix.

`euclideanNorm` explicitly uses the `WithLp 2` Euclidean norm. `lpNorm p y` is exactly `(Σ_i ‖y_i‖^p)^(1/p)` with real powers. `ratioSet` contains every ratio at every nonzero complex input; `inducedNorm` is its real `sSup`. The generic semantics theorem is unconditional apart from `m ≥ 1` and `p > 2` and applies to arbitrary complex `X` (even arbitrary output dimension).

The proof does the necessary nonvacuity work. A nonzero coordinate makes the denominator strictly positive. Every coordinate norm is bounded by the true lp norm using a monotone positive real-power equivalence. Triangle inequalities and finite sums give the concrete upper bound `Σ_iΣ_j ‖X_ij‖` for every ratio. The input vector of ones witnesses nonemptiness when `m ≥ 1`. The project then applies `isLUB_csSup`, `le_csSup`, and `csSup_le` with their actual proved conditions, yielding the least-upper-bound property, nonnegativity and the all-input inequality. The zero-input branch is handled using `p > 0`. No conditional-supremum default, assumed boundedness or restricted input set is exploited.

I retrieved pinned official Mathlib sources at `0df444a360eaa60ab8c11dca51a86af692955474`, with URL/hash provenance in `/private/tmp/nla-audit-187-192-mathlib/sources.json`. `PiL2.lean` confirms the Euclidean sum-of-squares formula; `Pow/Real.lean` confirms the inverse-exponent inequalities and `rpow_inv_natCast_pow` with nonnegative-base/nonzero-degree conditions; `Order/ConditionallyCompleteLattice/Basic.lean` confirms the genuine nonempty/bounded supremum theorems. `Matrix/Rank.lean` defines rank as the actual finrank of the complex linear range; `Matrix/NonsingularInverse.lean` identifies its actual inverse with a left inverse from an established product equation.

## Exact witness and global minimization

The matrices are unchanged:

`A = [[1,1,0],[1,0,1]]`,
`B = (1/3)[[1,1],[2,-1],[-1,2]]`,
`X = [[0,0],[1,0],[0,1]]`.

I independently reconstructed the rational matrix arithmetic without importing the submitted verifier: `AA* = [[2,1],[1,2]]`, the proposed Gram inverse multiplies to identity on **both** sides, `A* (AA*)⁻¹ = B`, `AB = AX = I₂`, `B ≠ X`, `B*B = (AA*)⁻¹`, and `X*X = I₂`. A 2-by-2 minor is one. The Lean proof likewise establishes actual invertibility and rank, using `rank(AX) ≤ rank(A) ≤ 2`; it does not define full row rank as possession of the proposed inverse.

With `q = sqrt(sqrt(2))`, positivity and `q⁴ = 2`, `q² = sqrt(2)` are proved. The real-power expression `2^(1/2-1/4)` is linked exactly to q. The project proves `lpNorm 4 y` raised to the fourth power equals the sum of true fourth powers, including zero coordinates. For all complex `y = (y₀,y₁)`, the inequality `‖y‖₂ ≤ q‖y‖₄` is exactly the nonnegative polynomial `(‖y₀‖²-‖y₁‖²)² ≥ 0`, with nonnegative roots used when returning from fourth powers to norms.

The actual complex action identities are

`‖By‖₂² + |y₀+y₁|²/3 = ‖y‖₂²` and `‖Xy‖₂ = ‖y‖₂`.

These give universal upper bounds for the true induced suprema. The nonzero norming vector `v=(1,-1)` maps under both B and X to `(0,1,-1)`, has lp norm q, and yields ratio `sqrt(2)/q=q`. The resulting upper and lower supremum bounds prove both exact induced norms equal q.

For **every complex** `Y` with `AY=I₂`, writing `t=(Yv)₀` forces `Yv=(t,1-t,-1-t)` and therefore `‖Yv‖₂²=2+3|t|² ≥ 2`. This proves `inducedNorm 4 Y ≥ q` without restricting Y to a displayed family or to real entries. Both B and X are consequently global minimizers, and q is an actual least element of the full feasible norm set. Specializing the original universal uniqueness statement to `m=2,n=3,A,p=4,X` would assert `q<q`, giving its negation.

An independent exact sparse-polynomial expansion in real and imaginary coordinates confirms the B action identity, the arbitrary complex competitor identity, and the fourth-power comparison residual. The code is `/private/tmp/nla-187-192-exact-check.py`, with all 14 checks passing in `/private/tmp/nla-187-192-exact-check.json`. These finite algebra checks supplement the read proof; they are not used as evidence of Lean elaboration.

## English scope and limits

The current page accurately distinguishes the manuscript's stronger all-p formulas/classifications from the formal result. A single admissible p=4 counterexample is sufficient for the complete negative answer to the original all-dimension/all-p uniqueness conjecture; the generic norm semantics nevertheless cover all original finite p>2. The exports additionally prove actual global minimality among every complex right inverse. They do not claim the manuscript's complete minimizer classification or all-p witness formula as Lean results. No hidden invertibility, denominator, boundedness, minimum-attainment, real-only, or norm-semantics premise weakens the conjecture.

Hashes of every read project source and the independent base/statement identity checks are saved in `/private/tmp/nla-187-192-source-checks.json`. Final publication acceptance remains contingent on the coordinator's independent CI provenance, exact-input binding and kernel/axiom audit; submitted PASS prose and bundled receipts were not treated as self-authenticating.
