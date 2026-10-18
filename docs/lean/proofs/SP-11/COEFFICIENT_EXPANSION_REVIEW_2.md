# Independent review 2: coefficient, monomial and coordinate-expansion gates

Reviewer: `/root/solved_inventory`, independent AI agent, 17 October 2026.
Verdict: **APPROVE the three support modules at the recorded hashes within their stated scope. No full SP-11 Target proof or status promotion is certified.** I did not author or modify these three modules.

I independently read the complete sources and ran fresh pinned Lean elaborations. [Machine-readable results](new-gates-review-2-evidence/result.json) bind commands, hashes, exit codes and logs. All three runs passed; every source was unchanged during its run. All selected LeanCert kernel assertions passed, and exported axiom reports contain only `propext`, `Classical.choice` and `Quot.sound`. These are local development runs, not fresh isolated Linux Comparator verification.

`MinorBasis` correctly identifies the actual determinant-basis coefficients. Distinct increasing coordinate tuples of the same finite size have different ranges, hence some coordinate of the first is omitted by the second. The corresponding matrix has a zero row, so its minor vanishes. Matching tuples give the identity matrix and determinant one. The finite sum consequently reads precisely one coefficient. Empty shape and impossible tuple types are retained through the definitions; no favorable-coordinate or injectivity premise has been silently inserted. The final universal-form equation identifies the advertised shared polynomial variable, with no numerical approximation.

`MonomialProducts` proves the conditional comparison needed to prevent compensation between reused variables: when every occurrence's actual variable is weakly later than its fixed best choice, and one is strictly later, the sum of occurrence exponents is strictly lower in the explicit lexicographic monomial order. The equality theorem relies on those pointwise one-sided comparisons; it does not infer them from equal aggregate histograms. The finite coefficient lemma correctly permits zero summands with the distinguished exponent while excluding other nonzero contributing summands. Its nonzero consequence needs no independence of occurrence names and assumes no unproved graph structure.

`GardenExpansion` expands actual alternating multilinear maps in the full coordinate basis, then specializes to a fixed output contraction coordinate. The incoming colors are summed exactly once and the output is not summed again. Its polynomialLSS recurrence invokes the real well-founded recursion and the same vertex-indexed coefficient form at every occurrence. The permutation theorem has the actual alternating sign and uses the first-output convention consistently. The repeated-color lemma derives zero from alternation; it does not introduce a fresh coefficient for a repeated tuple. The coordinate-subset/permutation presentation in the signed-variable lemma is an explicit premise, so future code must supply the actual sorting permutation for each injective color tuple.

These modules establish algebraic identities and conditional ordering facts. They do not yet supply a finite double-root occurrence model, prove the graph-specific per-occurrence bounds or the unique maximal shared-variable monomial, or prove that any required polynomial Gram entry is nonzero. All those remain necessary before the existing conditional reduction can produce the frozen Target.

The imported `AlternatingPolynomial` and `AlternatingContraction` modules were authored by this reviewer and have separate independent review obligations. This report binds their role as already checked dependencies but is not independent self-review of their contents. Canonical pages, IDs, originals, existing seven-module checkpoint sources, and target definitions were not edited.

| Reviewed source | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP11/MinorBasis.lean` | `98e16d2efb9f604e6df3c2e86f3a0544d9f21b12a91808a9051673d5a142dab6` |
| `lean-statements/NLA/Proofs/SP11/MonomialProducts.lean` | `734d5fa56b38d4b082b82b2312b668fa64cc88ee16dac3e12e931c47680ee915` |
| `lean-statements/NLA/Proofs/SP11/GardenExpansion.lean` | `1784dd6cfe2ae886781bd21599998439b5572f288287ec4df95cd4ba99d5d4ae` |
