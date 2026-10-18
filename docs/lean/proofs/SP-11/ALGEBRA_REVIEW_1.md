# SP-11 independent algebra review 1

Reviewer `/root/fr05_statement`, 17 October 2026. **APPROVE** the exact local
algebraic claims in `MinorBasis.lean` and `MonomialProducts.lean` at the hashes
below. Other agents wrote both modules. I read their complete source and
independently recompiled each with the pinned Lean 4.33.1/Mathlib/LeanCert
cache. Both builds passed their kernel assertions and reported only the
three standard axioms. [Commands and hashes](algebra-review-1-evidence/result.json)
and the separate logs are retained. Neither module proves full SP-11.

| File under `lean-statements/NLA/Proofs/SP11` | SHA-256 |
| --- | --- |
| `MinorBasis.lean` | `98e16d2efb9f604e6df3c2e86f3a0544d9f21b12a91808a9051673d5a142dab6` |
| `MonomialProducts.lean` | `734d5fa56b38d4b082b82b2312b668fa64cc88ee16dac3e12e931c47680ee915` |

`MinorBasis` correctly distinguishes equal increasing coordinate subsets
from distinct subsets. If every coordinate of one subset appeared in the
other, finite injectivity gives surjectivity and equality of their ranges;
strict monotonicity then gives equality of the tuples. Thus distinct subsets
omit a coordinate and the evaluated minor has a zero row. Matching subsets
give the identity matrix. The finite weighted sum therefore reads exactly
one specified coefficient. This includes arity zero and does not assume
independence of coefficients at different tree occurrences.

`MonomialProducts` compares sums of actual single-variable exponent vectors
in the lexicographic monomial order. Its weak inequalities require every
occurrence to weakly worsen; its strict inequality additionally requires
one strict worsening. Occurrence names need not be injective. Consequently
shared variable uses cannot compensate for a strict worsening under these
one-sided bounds. The equality criterion is valid by contradiction with the
strict result. The coefficient lemma permits zero summands with duplicate
exponents and isolates the unique *nonzero* summand of the distinguished
exponent. The polynomial is nonzero only after that distinguished summand's
coefficient is separately proved nonzero.

These are precisely local ingredients needed for the proposed garden
argument. They do not establish that canonical admissible conduit colors
exist or that every noncanonical coloring satisfies the required priority
comparisons. Those combinatorial claims and their connection to the actual
shared-variable polynomial recursion remain additional proof obligations.
No canonical problem, permanent ID, original statement or catalog status
was changed by this review.
