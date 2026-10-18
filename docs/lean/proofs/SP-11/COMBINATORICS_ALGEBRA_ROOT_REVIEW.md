# Independent combinatorics and alternating-algebra review

Reviewer: `/root`, OpenAI Codex AI agent, 17 October 2026.
Verdict: APPROVE for the support lemmas below. I implemented the other four
SP-11 modules and do not count this report as an independent review of them.

`GreedyOrdering` minimizes the number of nonneighbors in the chosen prefix
among remaining vertices. Finite strong induction deletes exactly the chosen
vertex; the membership and nodup proofs ensure a complete listing. Its stage
comparison holds against any still-unchosen vertex, and prefix inclusion gives
monotonicity. The position count is the literal number of earlier nonneighbors;
its interpretation as a list position uses the separate nodup/filter lemma.
For the last position in a complete nodup list, the earlier-nonneighbor set is
exactly the complement neighborhood. `degree_compl` therefore gives the exact
count-plus-one identity. Natural subtraction in the dimension bound is valid
because every degree is strictly below the positive vertex count. Minimum
degree is used only through Mathlib's actual `minDegree_le_degree`. No
connectedness, regularity, graph-family, or positivity restriction was inserted.

`AlternatingContraction` constructs an actual coordinate vector from the
basis evaluations of a linear functional. Expansion in the standard coordinate
basis gives its exact bilinear dot-product identity over any commutative ring,
including empty coordinate sets. Repeating the chosen prior vector in the
alternating form makes the value zero. This argument does not infer faithfulness
or independence from orthogonality.

`AlternatingPolynomial` uses determinants of selected increasing coordinate
subsets as alternating forms. The weighted finite sum and its application
formula are literal identities. Named polynomial coefficients are not assumed
independent for an arbitrary naming function; the separate PolynomialLSS
constructor provides the actual injective vertex/subset names. Reusing names
at repeated recursive occurrences retains shared variables. The output slot is
first rather than last, which alters only signs and leaves the reviewed zero
and nonzero obligations invariant. No non-cancellation theorem is imported.

I inspected these complete source files and the pinned Mathlib definitions
used by the proofs. Local Lean compilation and kernel assertions are separate
recorded evidence; I independently recompiled these three modules with the
pinned 4.33.1 runtime after inspection. They pass with the three standard axioms.
This is automated-agent review of support mathematics, not human peer review,
a proof of the full SP-11 target, or a Linux Comparator run.

## Reviewed source SHA-256

- `lean-statements/NLA/Proofs/SP11/GreedyOrdering.lean`: `89dfbb2d808ea85cf2a68e4e1790665a40ed3c55a860abd23309801ce0f19c21`
- `lean-statements/NLA/Proofs/SP11/AlternatingContraction.lean`: `5470ac391cec624ed4a11bc3fe5ff271dccbc2446db8a4aac44053c01407b6ca`
- `lean-statements/NLA/Proofs/SP11/AlternatingPolynomial.lean`: `d1ece1a3defce0f4cae49af934548c2bad20d7273a7df91b29111787d8c876f7`
