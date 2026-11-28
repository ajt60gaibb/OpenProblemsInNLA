# AC-12 — Audit of the order-eleven counterexample

**Source.** OpenBMB, [*An order-eleven counterexample to triangular realization of sign matrix permanents*](https://hexagonmath.org/2611.00424v1), deposited by Weiming Zhang, 13 November 2026. See [Theorem 1.1, Sections 2–4 and Appendix A](https://hexagonmath.org/pdf/2611.00424v1). The record identifies the manuscript as primarily AI-generated. This is an independent informal Codex review and exact computational reproduction.

## Witness

Let $C$ be the $4$-by-$4$ matrix with ones in positions $(i,i)$ and $(i,i+1\bmod 4)$, using zero-based indices. The sign matrix $J_{11}-2(C\oplus I_7)$ has permanent $P=2{,}029{,}568$. To check its value directly, for each column subset $S$ let $f(S)$ be the permanent on the first $|S|$ rows and those columns. Start with $f(\varnothing)=1$ and expand along row $|S|$ to obtain $f(S)=\sum_{j\in S}A_{|S|,j}f(S\setminus\{j\})$, with row numbers in this recurrence starting at one. Exact integer evaluation over the $2^{11}$ subsets gives $P$.

## Exhaustive exclusion

1. Normalize the last row of a triangular-pattern matrix to all ones by multiplying the last column by its bottom entry. This preserves the triangular sign condition and the absolute permanent.
2. With the bottom $r$ rows fixed, the first $11-r$ columns restricted to these rows are identical. The state $q_S$ records the permanent on those rows using active column set $S$ and $r-|S|$ common columns. When one extends the suffix upward, the rightmost common column becomes active and receives a free sign. Expanding a new minor along the added row contributes one term for each active column included, times its sign, and one term for each common column included. The latter terms have coefficient one and identical remaining minors. All predecessors are valid because a completion of the new minor uses one additional common column only when that column is available in the old suffix. This is recurrence (3.1), with a fixed zero at invalid state coordinates.
3. Each completed matrix has absolute permanent at most $(11-r)!\sum_S\binom{11-r}{r-|S|}|q_S|$. This follows by partitioning permutations by their columns in the last $r$ rows and bounding each complementary permanent by $(11-r)!$. Thus pruning strictly below $P$ cannot remove any desired matrix. Relabeling the active columns preserves all completion values because the entries above the suffix in those columns are independently free signs. The code canonicalizes only through these permutations and compares entire integer vectors when merging. Its twin shortcut uses transpositions that fix every valid state coordinate.
4. At $r=10$, there is only one common column. The eleven cofactors use all ten active columns or omit exactly one, and the first row may have any signs. The attainable values are all signed sums of their magnitudes. For magnitudes $a_i$, a sum equals $P$ precisely when a subset has sum $(\sum_i a_i-P)/2$. The negative target is excluded by sign symmetry.

## Reproduction

Save the C++17 listing from Appendix A as the source file below. I compiled and ran that listing with Clang. The checks use exact integers. At order eleven even the full permutation count $11!=39{,}916{,}800$ fits in the program's integer arithmetic.

~~~sh
mkdir -p results/pm1_permanent_range
c++ -O3 -std=c++17 tensor_target.cpp -o tensor_target
./tensor_target 11 2029568
~~~

The run matched every row of Table 1. At the last transition it examined 261,079,040 states before merging and rejected 254,731,228 by the complementary-minor bound. The final output was:

~~~text
final_profiles=34099 target_hits=0 verdict=EXCLUDED
~~~

The generated file `results/pm1_permanent_range/target_11_2029568_profiles.txt` had SHA-256
`9d4f210e19a5e0fbe3dd5475c17eddc4ed9680e4eb1d32cb5b37f021fae5fb8b`.
I checked all 34,099 distinct profiles again with integer subset-sum reachability, which gives an independent terminal test. The direct column-subset calculation above independently verified the witness. The finite exclusion and the witness together refute the original universal assertion.
