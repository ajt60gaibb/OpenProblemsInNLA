# MI-19 independent statement referee 2

**Verdict: approve.** The frozen definitions and two selected declarations faithfully express a genuine Hermitian positive-semidefinite counterexample over the complex numbers and the negation of the complete canonical subset conjecture. No statement change is requested. This is approval of the statement boundary before proof implementation, not certification of a completed Lean proof.

Reviewer: independent Codex agent `/root/leancert_examples`, 12 September 2026. The reviewer did not author these MI-19 statements and wrote no MI-19 proof code. This is agent review, not external human peer review or an official Tau Ceti service verdict.

## Frozen scope and source identity

| Reviewed file | Bytes | SHA-256 |
|---|---:|---|
| `NLA/MI19/Definitions.lean` | 3058 | `170e406d1f6bf0ca60e5b65998308b030cf08cc0def51c25c9860524ad3441ac` |
| `Challenge.lean` | 905 | `9c838a34cbff20eceb5e842eeca77c310bccb442843925343a7827a1020063cb` |
| `NUMERICAL_TARGETS.md` | 6986 | `cd93a4cefb529b69755c10bae600718442e0e6b8749c37df87c6dabec9b751aa` |

Read the complete canonical `matrix-inequalities-and-norms/MI-19/README.md` and Colbrook `matrix-inequalities-and-norms/MI-19/solution.tex`. Independently compared their current bytes with `git show` at upstream `5adea969c17391693978ada2674d25bb5c3daeb1`; both match. Their hashes are respectively `6102736589b7b36c1dd3579cb48cfba58ec07ac708c4ce0b9c50409e6172b77b` and `5d7278870da8bde55b87f77539e389ebb1dcc6debf3d1a588a00d7710e41ea0c`.

Read `reviews/statement-build.log`: `NLA.MI19.Definitions` and `Challenge` built successfully, 2159 jobs. Its only warnings are the two deliberately incomplete Challenge theorem bodies. The writer and root reported exit code zero; I independently read the log and observed the corresponding `.olean` files, but did not repeat the build. The solution had not been started when this review was completed.

The review applies [Tau Ceti semantic correctness](https://github.com/TauCetiProject/TauCetiReview/blob/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/rubrics/correctness.md), [scope](https://github.com/TauCetiProject/TauCetiReview/blob/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/rubrics/scope.md), and [Palomar definition fidelity](https://github.com/PalomarRegistry/PalomarPolicy/blob/e9c8c238f5695b10f75db7175648a1d0195352c1/prompts/03-definition-fidelity.md), adapted to this NLA repository's target rather than Tau Ceti's own roadmap.

## Definition and quantifier audit

- `inversionCount` examines **all** ordered pairs in `Fin n × Fin n`, retaining exactly those with `i<j` and `σ(j)<σ(i)`. Each inversion is counted once. `Fin` order is the original natural index order; adding one to every index recovers the paper's convention without changing inversions.
- `qPermanentTerm` has the correct power `(q:ℂ)^inversionCount σ` and the product of all entries `A i (σ i)`. Natural exponentiation retains `0^0=1`, including the allowed endpoint `q=0`. No determinant signs or absolute values are inserted.
- `qPermanent` sums over the full permutation type. `restrictedQPermanent` filters that same type by `S.image σ = S` and uses the identical term function. The predicate is setwise preservation. There is no reordering, complement renumbering, or replacement by a product of two smaller q-permanents.
- `SubsetConjecture` quantifies over every natural `n≥2`, every complex matrix satisfying genuine `Matrix.PosSemidef`, all real `q` in the closed interval `[0,1]`, and every nonempty proper finite subset. `S ≠ Finset.univ` is exactly properness because every such finite set is already a subset of the full finite index type. No real-only, positive-definite, positive-entry, singleton-only, or initial-segment restriction is imposed on the universal statement.
- I inspected `Matrix.PosSemidef` in pinned Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, `Mathlib/LinearAlgebra/Matrix/PosDef.lean`. It requires Hermitian symmetry and nonnegativity of the star-quadratic form for all finitely supported vectors. For `Fin n`, these are all complex vectors. It is not merely entrywise nonnegativity or nonnegativity on real test vectors.
- I inspected `Complex.le_def` and `Complex.lt_def` in `Mathlib/Analysis/Complex/Order.lean`: the scoped order compares real parts and requires equal imaginary parts. It is not a total or lexicographic order. The two explicit imaginary-part-zero conclusions in `counterexample` exclude a false refutation based only on nonreal incomparability.
- For the full Hermitian domain, the intended sums are indeed real: complex conjugation sends a permutation term to its inverse-permutation term; `inv(σ)=inv(σ⁻¹)`, the weights are real, and setwise preservation of `S` is closed under inverse. Pairing the finite sums therefore fixes them under conjugation. Thus the chosen partial complex order agrees with the ordinary real inequality in the canonical mathematical domain; no new reality premise narrows the conjecture. This paragraph is the reviewer's mathematical fidelity check, not a claim that a general reality lemma has already been formalized.
- `witness`, `gramFactor`, `witnessQ`, and `witnessSubset` are exact data, not assumed certificates. `gramFactor` has two rows and four columns, so the required conjugate-transpose product is a 4×4 Gram matrix. The actual entries are real inside `ℂ`; this legitimately produces a complex PSD instance.
- `witnessSubset={1 : Fin 4}` is exactly the paper's **interior** singleton `{2}`. For this singleton only, preservation amounts to fixing index 1. The general predicate remains setwise preservation and does not collapse to pointwise fixation for larger sets.

Inspected all ten definitions/abbreviations: `inversionCount`, `qPermanentTerm`, `qPermanent`, `PreservesSubset`, `restrictedQPermanent`, `SubsetConjecture`, `witness`, `gramFactor`, `witnessQ`, `witnessSubset`; and both exports: `counterexample`, `not_subsetConjecture`.

## Independent numerical reconstruction

Using only `itertools.permutations` and exact `fractions.Fraction` arithmetic, with matrices reconstructed from the source, I checked all 16 entries of `XᵀX=A`. I then independently enumerated all 24 permutations of positions `0,1,2,3`, counted every inversion in that full ordering, and selected the six permutations fixing position 1. No submitted checker was imported.

The independently recovered coefficient lists in **ascending** powers of q are:

- Full sum: `[4999700, 4886140, −199231, 4712758, 9568969, 4886140, 115600]`.
- Restricted sum: `[4999700, 4741130, 0, 4741130, 9482260, 4999700, 0]`.

They agree with both polynomials in the numerical-target draft and Colbrook's proof. At `q=7/8` the exact sums are

`P = 335001935775/16384`,

`R = 167502585675/8192`,

so `P−R = −3235575/16384 < 0`.

Every matrix entry and q is real, hence each finite term and both sums are real. The parameter lies inside the allowed interval; the singleton is nonempty and proper. The proposed exact Gram identity supplies PSD over complex vectors through `xᴴAx=(Xx)ᴴ(Xx)≥0`. These computations substantiate the frozen statements; they are not the future Lean certificate.

## Scope and decision

The counterexample export requires the actual full and restricted permutation sums, the exact complex rational gap, both reality facts, the strict reverse inequality, and all admissibility facts as **conclusions**. It does not assume the polynomial expansion, the Gram certificate, the negative gap, or the desired result. The optional polynomial formulas appear only as proposed proof reductions in the prose.

A real Gram witness belongs to the original complex PSD class, so its strict violation refutes the entire universal conjecture. The selected negation is not merely a statement about a restricted real or singleton conjecture. The manuscript's rank-two claim and positive-definite perturbation extension are expressly outside the chosen formalized claims; neither is necessary to settle the exact canonical yes/no problem negatively.

No vacuity, changed field, weakened quantifier, order mismatch, hidden numerical assumption, or shifted target was found. Proof implementation may begin on these exact hashes. Any subsequent definition or statement edit requires renewed review, and the completed proof still needs kernel/axiom verification, Comparator, and separate proof refereeing.
