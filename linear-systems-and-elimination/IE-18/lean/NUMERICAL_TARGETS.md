# IE-18 statement and numerical obligations

Statement draft prepared before proof implementation, 12 September 2026.
Formalization author: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. The counterexample and informal proof are due to Matthew J. Colbrook; their attribution remains in the canonical entry and manuscript. AI assistance is used for formalization. No human review or completed Lean proof is claimed at this stage.

The source of truth is the full canonical `linear-systems-and-elimination/IE-18/README.md` at upstream commit `5adea969c17391693978ada2674d25bb5c3daeb1`. The mathematical source is Section 2's first example in `references/colbrook-recovered-2026-09-11/manuscripts/IE-18.tex` at the same commit. The entire source, including its scope limitations and other results, was read before this draft.

## Original target, with its full quantifiers

`NLA.IE18.FourStepConjecture` quantifies over every natural dimension n≥2 and every nonzero symmetric real n×n matrix M for which the actual real spectrum omits 1. It states that the proposed pairwise value is the greatest member of the set of actual four-step Euclidean norm amplifications at all nonzero vectors.

Over real matrices, Mathlib's `Matrix.IsHermitian` is exactly symmetry. The definition uses the genuine `spectrum ℝ M`, rather than assuming a claimed eigenvalue list or imposing a stronger positive-definiteness hypothesis on all inputs. The full eigenvalue list comes from `hM.eigenvalues` in `Mathlib.Analysis.Matrix.Spectrum`: it retains algebraic multiplicities, and its particular enumeration is irrelevant to the maximum over every pair of distinct indices. The parameter `hM` is a proof of symmetry, not a spectral certificate carrying unproved numerical content.

The original maximum identity is expressed as

`IsGreatest (amplificationSet M) (pairMaximum hM)`.

Here `amplificationSet M` contains exactly the real numbers `euclideanNorm (R_M (R_M v)) / euclideanNorm v` with v≠0. `IsGreatest` requires both attainment of the proposed value and its upper-bound property for every such number. No empty-set or unbounded-set default for a real supremum appears.

This is the complete universal canonical assertion. The proof will refute it with one admissible matrix and vector; it will not merely negate an unrelated diagonal-only statement.

## Residual map and norm fidelity

For a coordinate vector v, define

`squaredNorm v = ∑ i, (v i)^2`,

`euclideanNorm v = Real.sqrt (squaredNorm v)`.

These are the actual Euclidean squared norm and norm. No use is made of the default norm on `Fin n → ℝ` or of the entrywise matrix norm.

Set A=I−M. `residualCoefficient M v` is the exact real quotient

`(vᵀ A v) / squaredNorm (A v)`.

`residualMap M v` explicitly returns zero when v=0, and otherwise returns `M (v−residualCoefficient M v • A v)`. This is the source's R map for **two original Anderson steps**. `fourStepResidual M v` is its actual composition with itself, accounting for four original steps. No recurrence equality, convergence statement, or numerically asserted residual is included as an assumption.

The coefficient is totalized at zero by real division, but that value is not used by the map's zero branch. On the original nonzero-vector domain, exclusion of 1 from the spectrum makes I−M invertible and therefore makes the squared denominator positive. In the concrete certificate, both actual denominators are computed as positive rational numbers before using the quotient. No division-by-zero artifact may supply the counterexample.

## Pairwise factor and square convention

Define

`pairQuotient a b = a*b*(b−a) / (abs(a*(a−1)) + abs(b*(b−1)))`,

`pairValue a b = (pairQuotient a b)^2`.

Real division makes a zero-denominator term zero, exactly as specified in the canonical page. In its admissible spectral domain this case can only involve two zero eigenvalues, since 1 is excluded. The use of a−1 rather than 1−a under absolute values does not change the expression.

`pairListMaximum μ` is the finite supremum, in nonnegative reals, of `‖pairQuotient (μ i) (μ j)‖₊²` over distinct indices i≠j, then coerced to the reals. The squared scalar nonnegative norm is the same real square as `pairValue`. For n≥2 the pair index set is nonempty, so this is exactly a finite maximum. `pairMaximum hM` applies it to the actual eigenvalue list. It does not drop repeated eigenvalue indices or silently alter the zero-denominator convention.

**The pairwise square is already part of the proposed unsquared norm amplification Λ. Therefore a comparison of squared Euclidean norms must use Λ², a second square.** The witness has Λ=1/121 and Λ²=1/14641. Comparing its squared norm amplification only to 1/121 would be the wrong target.

## Exact numerical data and obligations

All data are exact rationals interpreted in the reals. There are no floating-point inputs, interval approximations, or sampled matrix eigenvalues.

1. The matrix is `M=diag(1/10,1/2,3/5)` and the initial vector is `v=(1,1,1)`. Prove M≠0, real symmetry, and `1 ∉ spectrum ℝ M`. The counterexample also includes positive definiteness of both M and I−M, as true additional conclusions about this particular witness, not assumptions restricting the universal conjecture. Prove the exact spectrum is the range of the displayed diagonal entries; the actual full eigenvalue list is used by `pairMaximum`.
2. Prove v≠0. Compute the first actual denominator `squaredNorm ((I−M)v)=61/50` and coefficient `90/61`. Derive `residualMap M v = (−2,8,15)/61`, the vector named `witnessFirst`, directly from the map.
3. Prove `witnessFirst≠0`. Compute the second actual denominator `1381/93025` and coefficient `3140/1381`. Derive the actual composition `fourStepResidual M v = (289,−756,1125)/84241`, the vector named `witnessSecond`.
4. Prove the exact squared ratio of the actual four-step residual is `1920682/21289638243`. In detail the initial squared norm is 3, the final squared norm is `1920682/7096546081`, and dividing by 3 gives the displayed ratio.
5. The three unordered eigenvalue pairs have `pairValue` equal to `1/289`, `1/121`, and `9/2401`. Reverse ordered pairs have the same squared value. Use genuine spectral facts and a complete finite pair maximum to prove `pairMaximum hM=1/121`. Proving a value for a selected pair alone is insufficient.
6. Certify with LeanCert in explicit kernel mode that

   `1920682/21289638243 > 1/14641`.

   An equivalent exact integer certificate after clearing positive denominators is `28120705162 > 21289638243`, because `1920682*14641=28120705162`. The final proof may choose whichever exact scalar form yields a smaller kernel check.
7. Prove the nonnegative-square/square-root bridge to the **unsquared** inequality

   `pairMaximum hM < amplification M v`.

   This must use the actual Euclidean norm, the actual composed residual map, and positivity of the initial norm. No approximate square root is required.
8. Show the actual amplification belongs to `amplificationSet M`, contradict its proposed greatest element, and instantiate the complete universal assertion at this matrix to obtain `not_fourStepConjecture`.

An independent exact rational reconstruction during statement preparation confirmed both denominators, both coefficients, both residual vectors, all three unordered pair values, the squared norm ratio, and the integer cross-product above. This is evidence for the correctness of the draft; it is not a Lean proof.

## Selected exports and excluded stronger results

`residual_certificate` records the two actual map evaluations, denominator values, nonzero vectors, and the squared norm ratio. Candidate vector definitions are used only on the conclusion side of equalities; no such equality is assumed.

`counterexample` states the existence of a symmetry proof together with genuine matrix admissibility, both positive-definiteness conclusions, the exact spectrum, the exact actual pair maximum, a nonzero initial vector, the strict unsquared amplification violation, and failure of the corresponding `IsGreatest` statement.

`not_fourStepConjecture` negates the full original universal maximum identity. The parameter-family unbounded-underestimation result, the second semidefinite example, and the separate asymptotic-convergence question are outside this formalization's claims. They are not needed to settle the exact canonical yes/no target negatively.

## Statement gate, computation, and trust

The definitions and `Challenge.lean` must compile and pass two independent statement reviews **before** any proof implementation. Deliberate Challenge placeholders are confined to that separate target environment, which the eventual Solution must not import. Subsequent changes to these definitions or target statements require re-review.

Minimize computation by reducing diagonal matrix operations to exact rational coordinates and squared norms, and handling the finite pair maximum symbolically. No optimization over a sphere, root isolation, parameter interval, eigenvalue approximation, or interval subdivision is needed. LeanCert checks one scalar strict inequality after all semantic and algebraic reductions have been proved. The solution must use only a subset of `propext`, `Classical.choice`, and `Quot.sound`; native/compiler trust, `sorryAx`, and custom axioms are not permitted.

Source SHA-256 values: canonical README `ef32afd5788f56db1295284fba30de95e56478669f16513daed47535447ab7f0`; full Colbrook TeX `f7ebc6b6ebed015e24dfae48b0ed525fe67c99530a35ba66bed7d6ba44aa6b36`.
