# MI-16 independent Lean-boundary review

**Verdict: APPROVE.** I authored neither the MI-16 specification nor its Lean implementation. I independently checked the full live and frozen modules against the canonical README, approved specification, and Holden's `solution.tex` (especially Theorem 2.1 and Sections 3–5). This reviews the exact statement boundary and local elaboration, not a proof of Holden's theorem.

## Bound inputs

These are every path returned by `tools/lean_statements/check.py`'s `review_inputs` for MI-16's Lean-boundary phase, including the complete repository-local import closure and package pins.

| Input | SHA-256 |
| --- | --- |
| `matrix-inequalities-and-norms/MI-16/README.md` | `81cabc2257bb13297711002f19a88ef6b156b28a2fa23140dd5c118deacb10fc` |
| `docs/lean/statements/MI-16/ORIGINAL.md` | `81cabc2257bb13297711002f19a88ef6b156b28a2fa23140dd5c118deacb10fc` |
| `docs/lean/statements/MI-16/NUMERICAL_TARGETS.md` | `41fa41fc723c67443cbf64f3b0a4aad6b5090449866d886d0f99234e5668ab01` |
| `lean-statements/NLA/Statements/MI16.lean` | `59af0d9e2fcaba2b3540cc718804674d76737a2a554ceb307ef39c0038cd891f` |
| `lean-statements/Reviewed/MI16.lean` | `d363fbcd70b0ab340df8944571a9d2b0170bb878dbea11a60d5c3dc1f03cb1e0` |
| `lean-statements/NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |

`ORIGINAL.md` is byte identical to the canonical README. The frozen module is precisely the required header plus the live source with only its namespace changed.

## Semantic audit

The quantified dimension is `d+1`, so every `n≥1` is covered. The spectrum is an arbitrary ordered list of nonnegative reals, including zeros and repeated entries. `IsUnitary` is exactly the complex square-matrix equation `UᴴU=I`; `orbitMatrix` forms `Uᴴ diag(λ) U`; and Mathlib's matrix permanent is the complete permutation sum. The answer is an explicit spectral construction, not a `sup` over matrices, free oracle, or existence-only target. The final conjuncts assert attainment by a unitary, reality, and an upper bound for every unitary.

The coefficient field `IntermediateField.adjoin ℚ (Set.range spectrum)` specializes the actual eigenvalues before elimination. The multivariate variables are every matrix entry and a distinct `z`. `spectralEquation` multiplies `A−θI` once for each distinct eigenvalue. `permanentalAdjoint i j` deletes row `j` and column `i`, matching the source's differential convention. `criticalEquations` contains exactly the four families: power traces for all `k=1,…,n`, every entry of `qλ(A)`, every entry of `[A,C(A)]`, and `z−per(A)`.

`IsCriticalValuePolynomial` concretely characterizes the monic squarefree generator of the radical of the univariate elimination ideal: for every univariate `Q`, a positive power of its embedding lies in the critical ideal exactly when `P∣Q`. This is the same squarefree polynomial as the monic generator of `Iλ∩F[z]` followed by its monic squarefree part. It cannot be chosen to favor the desired answer. Positive degree and existence are asserted in `Target`, without taking them as hypotheses. The roots are interpreted in `ℝ` only after this construction.

The moment formula is finite and concrete. `homogeneous` enumerates all exponent vectors of total degree `j`; `schur` uses the descending partition parts and Jacobi–Trudi determinant with negative-degree entries set to zero. `fullCycleLengths` adds the fixed one-cycles omitted by Mathlib's `cycleType` (confirmed against Mathlib's `sum_cycleType` and `cycleType_one`). The Frobenius alternant coefficient gives the ordinary integer character of `S_m`; its exponent vector is partition parts padded with zeros plus `(m−1,…,0)`. `momentWeight` uses `fν/m!` and the exact double sum of `χ(kh)` for the explicit row and column permutations. `spectralMoment` sums only partitions of `m=np` with at most `n` rows and divides by the corresponding `sν(1ⁿ)`. `Target` includes denominator positivity for every positive moment order. No Haar integral or limit is left in the answer.

The selector covers the zero spectrum, a single candidate, and multiple candidates. In the latter branch it takes distinct real roots in the **closed** interval `[0,B]`, where `B=(max λ)^n`; computes the minimum adjacent gap; chooses the least natural `b` satisfying `2^b≥1+16n²B/ρ`, `h=ceil(4B/ρ)`, and `p=2n²bh`; then telescopes the gaps with the strict test `T(n,p,λ)>rⱼ^p`. These match `solution.tex` lines 133–166. The `Target` conjuncts establish nonempty roots for a nonzero spectrum, positive gap and existence of the qualifying `b` when multiple roots exist. The root list retains potentially infeasible complex-critical values, as the source requires.

I built `NLA.Statements.MI16` and `Reviewed.MI16` under the pinned Lean 4.33.1 toolchain; both succeeded. `#assert_statement` and LeanCert `#assert_trust kernel` passed. Both axiom reports list only `propext`, `Classical.choice` (printed as `choice`), and `Quot.sound`. This does not prove the exact-value theorem and is not isolated Comparator verification.
