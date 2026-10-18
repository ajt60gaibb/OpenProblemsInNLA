# Independent greedy-transport and monomial review

Reviewer: `/root`, OpenAI Codex AI agent, 17 October 2026. APPROVE for these
support gates. I did not implement either reviewed module. This review proves
no complete catalog target and does not review my own other proof modules.

`GreedyRelabel` uses an actual permutation of `Fin n` from a complete nodup
listing. The image of each natural prefix is proved equal to its list prefix;
this transports finite nonneighbor counts and the exact greedy comparison.
The graph is Mathlib's actual comap, with minimum degree transported through
its graph isomorphism. Simultaneous matrix reindexing preserves ordinary real
rank, symmetry and both directions of the off-diagonal pattern condition.
Positive n supplies the last vertex for the dimension calculation. No external
ordering oracle or renamed abstract invariant supplies these results.
The final theorem explicitly assumes precisely the remaining ordered
shared-variable polynomial noncancellation statement, then obtains the full
frozen matrix witness. It does not prove that premise.

`MonomialProducts` compares finite sums of single-variable exponents in
Mathlib's lexicographic monomial order. The reversed priority of variable
indices agrees with Finsupp.Lex.single_le_iff/single_lt_iff. Its finite
occurrence set need not have injective variable names: pointwise weak
worsening and one strict worsening give strict worsening of the complete
exponent sum, so no other occurrence can compensate. The equality-rigidity
corollary follows by contradiction. The coefficient lemmas correctly retain
only uniqueness among nonzero contributions to the distinguished exponent;
zero-coefficient colorings may share it. They establish a coefficient identity
and nonvanishing only after their explicit uniqueness premises are proved.
A linear order with reverse well-foundedness remains required of variable
indices. The finite actual graph coefficient type must still receive the
appropriate vertex/tuple priority order; these generic lemmas do not assert it.

I inspected both complete files and their pinned Mathlib APIs, and independently
recompiled them with the pinned runtime and kernel assertions. These exact
algebraic/combinatorial support gates need no interval certificate. Only
foundational axiom subsets occur. The graph-specific expansion, admissibility,
and classwise uniqueness argument remain necessary for noncancellation.

## Reviewed SHA-256

- `lean-statements/NLA/Proofs/SP11/GreedyRelabel.lean`: `7e2cfe0f41f619bae813d77469bba03c80dac43885e47c652e7e59b0fd09ee0a`
- `lean-statements/NLA/Proofs/SP11/MonomialProducts.lean`: `734d5fa56b38d4b082b82b2312b668fa64cc88ee16dac3e12e931c47680ee915`

## Exact coordinate-expansion review

`GardenExpansion` expands the actual alternating multilinear form in its
standard coordinate basis. Scalar factors are products of the original
coordinates. Applying that identity to the curried output slot gives the
contraction expansion with only input colors summed. Rewriting the proved
well-founded recursion yields the literal `polynomialLSS` expansion using
`vertexCoefficient`, which calls the existing vertex-indexed form; repeated
occurrences do not receive new variables. Permuting an increasing basis tuple
gives exactly its alternating permutation sign and the same coefficient
variable. Noninjective colors repeat a vector and force zero. These gates do
not assert that an arbitrary injected tuple has already been sorted, or that
a nonzero coloring has a unique exponent. Those are further explicit proof
obligations. I independently inspected and recompiled this other-agent module.

- `lean-statements/NLA/Proofs/SP11/GardenExpansion.lean`: `1784dd6cfe2ae886781bd21599998439b5572f288287ec4df95cd4ba99d5d4ae`
