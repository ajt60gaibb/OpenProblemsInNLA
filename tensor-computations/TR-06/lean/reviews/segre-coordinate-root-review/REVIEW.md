# Independent exact-dimensional Segre contribution review

Reviewer: root, nonauthor of these implementation modules or Complexification. APPROVE SegreCoordinates.lean SHA256 `32a7e743d22711ac45d649b104faaf99417ac039389e8455049dc47e794ad04a` and SegreNonzero.lean SHA256 `b20f7cf0653882416e84c87b669766a66f2d89bc8fad585c6b5b7e8ccad83412`, with unchanged approved SegreBoundary.lean `792666bb6115b2353738ec54b3a6577e580639945dcb28e4f3ee12443eadefe7`.

Read both complete implementations. The cardinal computation proves exactly one amplitude plus each non-anchor coordinate per summand; Euclidean real and complex finranks are exactly k. Polynomial evaluation and substitution match the actual decoded summands and their sum. Decomposition status uses d>0 only to absorb amplitude; reconstruction normalizes the supplied actual factor witnesses at proved nonzero pivots and also retains permitted d=0 cases.

Nonzero pullback is established for every prescribed pattern. The original actual decomposition witnesses a nonzero raw-factor pullback polynomial. Its product with the nonzero prescribed pivot-variable product has a nonzero complex evaluation. This makes all actual tensor pivots nonzero, enabling exact normalized reconstruction, so the exact-dimensional pullback is nonzero. Raw coordinates are used only for algebraic existence, not a dimension or measure bound.

The real-witness theorem uses infinite real-subfield polynomial density, valid even with no variables, on the product of amplitudes and pullback. It proves every real amplitude nonzero, constructs an actual decomposition, and explicitly proves scalar extension of its sum equals complexification. It makes no unsupported exact-real-rank or real-identifiability claim. No boundary or final hypothesis changed.

Fresh sequential rerun of copied Complexification, frozen boundary and both proof modules exited0 without warnings. All advertised statement closures and real-density closure contain only the standard permitted three axioms and pass LeanCert kernel assertions. Evidence is local and uses pinned dependency caches; complete TR-06, tensor nullity, Linux Comparator and independent kernel replay remain unproved.
