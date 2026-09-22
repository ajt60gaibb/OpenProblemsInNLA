# TR-27 integral-image author evidence

Author: AI proof-author agent `/root/reference_review`, acting within the George Stepaniants formalization campaign. This is author evidence, not an independent proof review. The agent independently approved the frozen mathematical boundary before becoming a TR-27 proof author, and cannot count as an independent final full-proof referee.

The new `NLA/TR27/IntegralImage.lean` proves the exact frozen `substitution_integral` and `whole_closed_image` declarations. It imports `Algebra.lean`, never `Challenge.lean`. It changes none of the mathematical files bound by the preproof freeze.

The monic quadratic has coefficient polynomials `(8 H₀ + 9 H₂)/85` and `−5 H₀²/85`, and its root is `s¹²`. Exact kernel-checked polynomial normalization establishes the identity. The integral closure contains `s¹¹t = (5s¹²−H₀)/3`, then `t¹² = (H₁₂ + 535538s¹¹t)/5`. Positive-power integrality gives both parameters; multivariate polynomial induction gives the complete substitution map's integrality. The proof does not assume injectivity of the substitution.

For every point in the full zero locus of the kernel, its evaluation maximal ideal contains that kernel. Integral lying-over produces a maximal ideal of the two-parameter polynomial ring above it. The complex Nullstellensatz realizes that ideal as evaluation at a complex parameter pair, and the coordinate equations recover the original point. The reverse inclusion follows evaluation of the kernel. This proves equality with the entire zero locus, with no omitted chart, extra component or nonzero-coordinate assumption.

The second equality uses the exact degree-twelve scaling law, both finite and infinity charts from `Algebra.lean`, and existence of complex twelfth roots for every scalar. The zero parameter and zero cone vector are treated explicitly; arbitrary nonzero cone scalars are unrestricted.

A fresh local macOS Lean 4.33.1 build compiled Definitions, Algebra, IntegralImage and an external axiom audit in a separate output directory. All twelve public declarations have exactly `propext`, `Classical.choice`, `Quot.sound` in their transitive axiom closures. There are no `sorry`, `admit`, native-decision calls, added axioms or target assumptions in this module. No LeanCert numerical tactic is needed for these exact algebraic proofs; this receipt does not claim a completed LeanCert verifier run.

The retained script reproduces this local development check using the campaign's installed pinned package artifacts. It is not the authoritative Linux driver, complete-problem Comparator run, independent final proof review or full TR-27 verification. Those are not run by this bounded author task. The generic semantic bridges and rank/lower-bound obligations remain outside this module; no status promotion or PR is authorized by this evidence alone.
