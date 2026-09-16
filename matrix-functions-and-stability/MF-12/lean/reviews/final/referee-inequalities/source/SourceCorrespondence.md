# MF-12 source correspondence

Status: the complete reviewed proof graph passed actual Linux development run
35034380090 at a1efcbfc59263b9e5bb00914ee709112348c1e54. Standalone canonical
verification remains pending. Every entry below is implemented at the unchanged
frozen Challenge signature; the original draft is preserved in statement-audit.
The canonical target and complete authored manuscript are pinned at
8f04b905eb2e0827b6b84f37d9d080ae1f05b202; SOURCE-PROVENANCE.json binds their bytes.
Original proof: Matthew J. Colbrook, University of Cambridge DAMTP.
Formalization: George Stepaniants, California Institute of Technology CMS.

| Implemented declarations | Source and exact purpose |
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

Definitions and all 28 independent signatures were reviewed by two independent
agents and actually elaborated on non-root Linux in run 35026411039 before the
immutable freeze and any proof implementation. The exact originals, statement
reviews, source provenance and pre-proof receipt remain in statement-audit/.

All 19 Solution closure files now match the actual successful development inputs
at a1efcbfc59263b9e5bb00914ee709112348c1e54. Every target passed its LeanCert
kernel-trust assertion. The exact observed axiom set for gap_decomposition is
propext/Quot.sound; the other 27 use the standard three. All 28 textual types
match the frozen Challenge, and the Solution closure contains no holes, custom
axioms or Challenge import. The full source review chain, proof-only repair
addenda and independent actual-log reconciliation are retained under reviews/.

Preparing this standalone package changes only metadata, source-correspondence
status text and the default Lake target from Challenge to Solution. The exact
before versions are retained under verification/packaging/before/. It does not
change any mathematical definition, signature, proof byte or dependency pin.
The packaging reviewer contributed no mathematical implementation.

Standalone Comparator must still compare all 28 exports without replaceable
definition holes; independent default-kernel replay and negative controls are
also pending. Both independent complete mathematical source reviews approve
these exact proof bytes. Two final source/evidence referee verdicts remain
necessary after the actual standalone canonical checks. Complete development
compilation is not a claim that these canonical gates have already run.
