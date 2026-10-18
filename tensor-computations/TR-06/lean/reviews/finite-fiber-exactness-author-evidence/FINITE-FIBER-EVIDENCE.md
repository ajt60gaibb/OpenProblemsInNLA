# Finite complete fibers force exact rank: implementation evidence

All six propositions in the independently approved FiniteFiberExactnessBoundary.lean are now proved in FiniteFiberExactness.lean, with the original definitions and hypotheses unchanged. This is a supporting contribution and does not complete TR-06.

The final exact_rank_statement proves frozen ExactRank r A over any RCLike scalar field, under d > 0, every mode size positive, r >= 2, and finiteness plus nonemptiness of the entire existing closedAdditionFiber r A. It uses Set.Finite and Set.Infinite, never a finite Nat.card convention.

rank_bound_statement removes all zero entries from a chosen member of any nonempty closed fiber, producing an actual decomposition of length at most r. split_family_statement proves that the exact approved splitTuple family is injective for every scalar and lies in the complete fiber whenever 0 < m < r and a is an actual length-m decomposition. It retains all zero entries at t = 0 and t = 1. The proof derives the sum identity by splitting off the two first positions, retaining exactly the remaining m - 1 terms, and proving every padded position contributes zero.

unit_tensor_statement proves the actual all-ones pure tensor is nonzero when mode sizes are positive. cancel_family_statement uses the exact approved cancelling tuple family t*B, -(t*B), followed by zeros; the family is injective and sums to zero for every scalar. Scalar absorption reuses the already independently reviewed Segre.pureTensor_smul_mode helper and explicitly requires d > 0.

shorter_infinite_statement handles positive shorter length through splitTuple and empty shorter length through the cancelling family after proving A = 0. Each proof exhibits the range of an injective map from the infinite scalar field contained in the full fiber. exact_rank_statement then rules out every shorter decomposition by contradiction with Set.Finite, and uses the rank bound to obtain a length-r actual decomposition. The output is exactly both clauses of frozen ExactRank.

Frozen boundary SHA256: 96b4045af8b02e01d235849609f523437ee84f30cfb0e2dc5f6614b2b5babc51. Final implementation SHA256: eeae8de29b1390c7ee63f9b43913a3e489bd3934ceeeb0cb78deb6ce9f834a9a. Pre-proof approved boundary, plan and root review are retained byte-for-byte in evidence/finite-fiber-approved/.

The final seven-module sequential pinned Lean 4.33.1 rerun is recorded in evidence/024 through 030. Definitions, Complexification, ClosedFibers, SegreBoundary, SegreCoordinates, FiniteFiberExactnessBoundary and FiniteFiberExactness all exited zero with no warnings. All six new theorem closures are exactly propext, Classical.choice and Quot.sound, and all six LeanCert #assert_trust kernel assertions pass. FINITE-FIBER-EVIDENCE.json records source hashes, exact commands, LEAN_PATH and log hashes. Earlier development errors and the subsequently removed unused-simp warning remain honestly recorded in older logs.

Independent post-proof review is still required; this file is the implementer's evidence, not an independent approval. No sorries, admits, custom axioms, native_decide, altered frozen definitions or weaker targets were introduced. This does not yet establish actual finite/nonempty fibers at every desired localization point, identifiability, real properness, derivative injectivity, smooth-locus correspondence or integral finiteness.

Formalization credit: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. Original TR-06 mathematical proof attribution: Matthew J. Colbrook. No contact email is included.
