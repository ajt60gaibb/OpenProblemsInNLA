# MF-12 source correspondence

Status: proof-free statement package. No independent approval or Lean execution
is claimed. Every entry below is a proposed Challenge obligation, not a result.
The canonical target and complete authored manuscript are pinned at
8f04b905eb2e0827b6b84f37d9d080ae1f05b202; SOURCE-PROVENANCE.json binds their bytes.
Original proof: Matthew J. Colbrook, University of Cambridge DAMTP.
Formalization: George Stepaniants, California Institute of Technology CMS.

| Proposed declarations | Source and exact purpose |
|---|---|
| `family_growth_is_maximum`, `pair_word_norms` | Canonical Context and notation; manuscript section1. Prove actual finite, nonempty attained maxima and every admissible product, with no binary-word restriction hidden in the family definition. |
| `entry_maximum_norm_comparison`, `tensor_norm_comparison` | Explicit formal proof simplification for sections3 and5. Actual finite entry maxima mediate genuine Euclidean operator norms; fixed dimension factors replace unproved spectral-norm Kronecker multiplicativity. |
| `tensor_word_identity` | Section5 exact Kronecker product of every switching word, with a specified Fin(d*e) coordinate equivalence. |
| `fractional_parameters`, `fractional_projection`, `jordan_two_power`, `compressed_powers`, `loss_gain_bounds` | Section2 and lemma `lem:compressed`. The exact original arrays, unrestricted q=0 power identity, fixed lambda=1/4 and arbitrary real alpha in (0,1) are retained. |
| `telescoping_budget`, `compressed_product_formula`, `compressed_product_bound` | Lemma `lem:budget`; exact later-gap weights, complete ordered product and finite Holder bound, including empty and zero gaps. |
| `fractional_powers_entry_bound`, `gap_decomposition`, `reset_product_factorization`, `fractional_all_word_upper` | Section3. The full chronological word splits into arbitrary gaps, and the actual reset reduction controls all words. C=1728/(1-mu)^2 is a deliberate sufficient enlargement of the source constant. |
| `logarithmic_gap_bounds`, `bernoulli_loss`, `lower_word_exact`, `fractional_lower_all_lengths` | Section4. Exact integer logarithm/division gives a prescribed word at every length. A rational Bernoulli argument gives lost mass>=1/5 and c=(1/4)^alpha/10, replacing the sharper exponential constant. Small positive lengths remain included. |
| `fractional_growth_estimates`, `roots_of_polynomial_growth` | End of section4 and canonical JSR definition. The actual finite maximum obeys both bounds, and the actual nth-root sequence converges to one. |
| `jordan_entries`, `jordan_growth_estimates`, `integer_family_growth` | Section5, lemma `lem:Jordan`. All natural m, n>=1, n<m and m=0 are retained. The integer pair includes zero as a distinct second generator. |
| `fractional_tensor_growth` | Section5 noninteger construction with the actual lifted generators. Fixed dimension factors weaken constants only, preserving exponent alpha+m and all lengths. |
| `realizes_every_nonnegative_exponent` | Complete canonical problem and the existence/comparability/JSR portion of theorem `thm:main`: every real gamma>=0, fixed finite real family of cardinality two, all n>=1, and actual root limit one. |

The source's dyadic-rational-entry corollary, rational pairs with particular
irrational exponents, density corollary, sharper constants, and optimal-dimension
questions are not proposed exports. None is required by the retained canonical
question. No unproved outside theorem is an intended assumption.

Definitions and all28 proposed signatures require two independent source
reviews and actual remote Linux elaboration before an immutable freeze and any
proof implementation. Comparator must compare all28 exports without replaceable
definition holes; final acceptance also requires all LeanCert kernel assertions,
standard-axiom reports, default-kernel replay, negative controls and two final
independent referees. This package claims no completed verification.
