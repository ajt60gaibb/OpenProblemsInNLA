# Five-tail trimming concentration author milestone

Author: AI agent `reference_review`. This is author evidence and is not an independent final proof review.

- `NLA/IE21/BoundedConcentration.lean`: SHA256 `1b0eea5beaabaefd8dd6b15df3f5b4a71eb620f9ee13b67949c467c96675c7b3`.
- `NLA/IE21/TrimmingConcentration.lean`: SHA256 `04828fc5953c3814a12abbe5056d90cddd2208d0bf1b94d6fc904f9543721c83`.

The three bounded Hoeffding declarations retain the exact exponent `-2*m*ε^2`, with interval length explicitly present in the deviation threshold. The full generic `independent_trim_concentration` applies to arbitrary independent copies with the literal common law and to every nonnegative integrable variable with mean one. It retains the source's exact error `2*L*ε + L/m`, failure bound `5*exp(-2*m*ε^2)`, `L=2/(1-θ)`, and complete range `0<ε≤(1-θ)/2`.

A bounded threshold quantile supplies a selector W with values in [0,1]. A fractional value on a quantile atom preserves exact mean θ. Its selected energy YW has values in [0,L], and its expectation equals the actual frozen threshold-dual populationTrim. Hoeffding supplies two tails for W and two for YW. The count indicator of Y≤L supplies one lower tail. Its mean is at least θ+ε by the pointwise Markov inequality `L*(1-C)≤Y` and the given ε range. Thus a good count event supplies at least the exact floor(θm) observations. The proved deterministic finiteTrim comparison and the floor error at most one give the original error bound. Empty retained sets, quantile atoms, ties, and equality at the upper ε endpoint are included.

The retained fresh macOS author build compiles all local prerequisite sources against cached pinned dependencies. Six public declarations have their full axiom closures printed and checked against the three permitted axioms. Receipt and full command/output hashes are in `concentration-author-evidence.json` and `concentration-typecheck.log`. This milestone does not run Comparator or LeanCert, does not rebuild dependencies from source, and does not establish the complete IE-21 package or change status. The mathematical boundary files remain frozen.
