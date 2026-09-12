# IE-18 independent statement referee 2

**Decision: approve the frozen statement for proof implementation.** This is an independent AI-agent statement review dated 12 September 2026, not external human peer review, a completed Lean proof, or an authoritative Linux Comparator result. The reviewer did not author the definitions, target statements, numerical plan, or proof. No mathematical source was changed during this review.

The reviewed upstream source is commit `5adea969c17391693978ada2674d25bb5c3daeb1`. The full canonical IE-18 README and the entire Colbrook manuscript were read, including the additional parameter-family result and the explicit exclusion of the asymptotic convergence question. The complete source-file hashes are recorded in [the input manifest](statement-referee-2-evidence/inputs.sha256.json).

| Frozen input | SHA-256 |
| --- | --- |
| `NLA/IE18/Definitions.lean` | `dc32a03d0ab95a1b3f41f864f90d30d56c3dd041330015caa059e253ff47b28d` |
| `Challenge.lean` | `97ad7cf8e2c3077d4cc52f587c9702627f06c8d915005804f044fd60c66ffd59` |
| `NUMERICAL_TARGETS.md` | `318f34ec1f88f111a83c1a6c869735ac2cc5640b5bdb34f89201e97607e9e890` |
| Canonical IE-18 README | `ef32afd5788f56db1295284fba30de95e56478669f16513daed47535447ab7f0` |
| Full Colbrook `IE-18.tex` | `f7ebc6b6ebed015e24dfae48b0ed525fe67c99530a35ba66bed7d6ba44aa6b36` |

## Fidelity to the original assertion

`FourStepConjecture` includes every original quantifier and hypothesis: every natural dimension at least two, every nonzero real square matrix, real symmetry, and exclusion of one from the actual matrix spectrum. It does not restrict the universal statement to diagonal matrices, contractions, positive definite matrices, chosen spectra, or selected initial vectors. The positive definiteness conditions in `counterexample` are additional conclusions about its particular witness. They do not weaken the conjecture being negated.

The residual coefficient is exactly `vᵀ(I−M)v / ‖(I−M)v‖₂²`, using the ordinary matrix-vector product and dot product. `residualMap` handles zero explicitly and otherwise implements the stated map. Its actual composition with itself is the four-step residual. Candidate residual vectors occur as definitions on the conclusion side of equalities, not as unproved premises. Excluding one from the spectrum makes `I−M` invertible; for nonzero inputs the denominator is consequently positive. The certificate additionally requires both concrete denominators to equal strictly positive rationals, so no zero-division convention can generate this counterexample.

`euclideanNorm` is the square root of the sum of coordinate squares. This represents the Euclidean norm and avoids the different default norm on a function type. The final target compares unsquared norm amplifications at all nonzero vectors. `IsGreatest` requires membership and an upper bound for every member of `amplificationSet`; it preserves both attainment and the universal upper-bound content of the original maximum, without using a totalized supremum on an empty or unbounded set.

The pairwise factor is computed from Mathlib's actual full eigenvalue list. The maximum includes every ordered pair of distinct indices, including repeated eigenvalue values. Squaring makes reversing the order immaterial. Real division supplies exactly the canonical zero-denominator convention. `pairListMaximum` folds finite maxima of nonnegative squared absolute values; the pair index set is nonempty for every permitted dimension. Coercing these squared absolute values to the reals gives the square in the original formula.

The exported `not_fourStepConjecture` negates the complete original assertion. A single admissible strict violation suffices for this negative resolution. The manuscript's unbounded-underestimation family, second semidefinite example, and separate asymptotic question need not be formalized to prove that target, and the numerical plan explicitly excludes those stronger or separate claims.

## Imported semantics checked

The review inspected the actual pinned Mathlib source at `0df444a360eaa60ab8c11dca51a86af692955474`, rather than relying only on names or docstrings:

- `LinearAlgebra/Matrix/Hermitian.lean`: `IsHermitian` is equality with the conjugate transpose; `isHermitian_iff_isSymm` supplies the real symmetric interpretation.
- `Analysis/Matrix/Spectrum.lean`: `eigenvalues` reindexes the spectral-theorem list associated with a full orthonormal eigenvector basis; `roots_charpoly_eq_eigenvalues` retains characteristic-polynomial root multiplicities, and `spectrum_real_eq_range_eigenvalues` identifies the actual real spectrum.
- `Algebra/Algebra/Spectrum/Basic.lean`: spectral membership is noninvertibility of the scalar identity minus the matrix. In particular, excluding one is the required invertibility condition for `I−M`.
- `LinearAlgebra/Matrix/PosDef.lean`: positive definiteness includes Hermitian symmetry and strict positivity of the quadratic form on all nonzero vectors; its finite-dimensional dot-product characterization agrees with the witness claim.
- `Data/Finset/Lattice/Fold.lean`: the finite `sup` folds the lattice maximum from the bottom element. On nonnegative reals it gives the required finite maximum, with no real-supremum default issue.
- `Analysis/Normed/Group/Real.lean` and `Analysis/Normed/Group/Basic.lean`: the real norm is absolute value, and the coercion of `nnnorm` is that norm. Thus the squared scalar norm used by the pair maximum is exactly the real square.
- `Order/Bounds/Defs.lean`: greatest elements require membership and an upper bound for every element of the set. `Data/Matrix/Mul.lean` uses the standard finite dot product and row-wise matrix-vector multiplication.

## Independent numerical reconstruction

The reviewer independently executed both residual steps using Python's exact `fractions.Fraction` arithmetic and generic full matrix-vector multiplication. No supplied residual was used as an assumption of that computation. The complete output is in [the rational reconstruction record](statement-referee-2-evidence/exact-rational-reconstruction.json); this auxiliary check is not a Lean proof.

The computation obtained first denominator `61/50`, coefficient `90/61`, and residual `(-2,8,15)/61`; then second denominator `1381/93025`, coefficient `3140/1381`, and actual four-step residual `(289,-756,1125)/84241`. All three unordered pair values are `1/289`, `1/121`, and `9/2401`, so the proposed factor is exactly `Λ=1/121`. All diagonal eigenvalues lie strictly between zero and one, making both matrices positive definite and excluding one from the spectrum.

The actual squared norm ratio is `1920682/21289638243`. The essential comparison is against **`Λ²=1/14641`**, because the square in the pair formula is already part of the proposed unsquared norm amplification. The exact cross-product is `1920682*14641 = 28120705162 > 21289638243`; the positive rational gap is `6831066919/311701593515763`. The target correctly requires a proved bridge from this squared comparison to the strict unsquared Euclidean norm inequality. It does not make the erroneous comparison against `1/121` at the squared-norm stage.

## Type checking and remaining proof gate

Independent `lake env lean NLA/IE18/Definitions.lean` and `lake env lean Challenge.lean` checks use Lean 4.33.1. The deliberate three Challenge placeholders remain confined to the target environment and are expected at this statement stage; they are not verified solution proofs. Commands, exit codes, tool version, exact logs, and dependency revision checks are recorded in [the independent check record](statement-referee-2-evidence/checks.json). Each locked dependency's checked-out revision matches its manifest revision and has no tracked modification.

The computation plan is appropriately small: exact rational coordinate identities, a complete finite pair maximum tied to genuine spectral facts, one scalar strict inequality certified by LeanCert in explicit kernel mode, and an analytic square-root bridge. It needs no eigenvalue approximation, interval subdivision, root search, or optimization over vectors. This is a plan approval; its implementation and transitive axiom closure still require independent proof review and the authoritative Linux Comparator check with the standard-three whitelist.

No blocking statement issue was found. The approval binds only to the hashes above. Changes to either definitions or target declarations must reopen the statement gate. It does not authorize marking an unproved target Lean verified.
