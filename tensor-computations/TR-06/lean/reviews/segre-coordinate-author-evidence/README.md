# Segre coordinate and nonzero-pullback contribution

All six propositions in the root-approved SegreBoundary.lean are proved without changed definitions or hypotheses. This is supporting progress for TR-06, not complete-target verification.

SegreCoordinates.lean proves dimension_statement, evaluation_statement, decomposition_statement and representation_statement. The actual parameter is EuclideanSpace over one amplitude and all off-pivot factor coordinates for each summand. Its real and complex finranks equal r * (1 + sum_j (n_j - 1)). Decoding uses actual nonzero rank-one tensors, with the amplitude absorbed into a genuine mode when d > 0. Reconstruction works over every RCLike field and requires no positive-mode assumption.

SegreNonzero.lean proves nonzero_pullback_statement and real_witness_statement. From one actual complex decomposition on which p is nonzero, the pullback is nonzero for every prescribed pivot pattern, even one with zero entries in the supplied witness. An auxiliary raw-factor polynomial is multiplied by every desired pivot variable to exhibit a suitable complex evaluation, then normalized into the exact-dimensional parameter space. Raw factors are used only for this existence step. Polynomial density of the real subfield then gives an actual real parameter with every amplitude nonzero and p(complexify(sum)) nonzero. No universal real/complex rank equality is asserted.

All statements include rank r = 0. The decoded-decomposition and real-witness statements retain exactly the approved assumption d > 0. The representation and nonzero-pullback statements include d = 0. No positivity on mode sizes is added; the prescribed pivot pattern itself supplies the required indices whenever summands exist.

Final source hashes:

- SegreBoundary.lean: 792666bb6115b2353738ec54b3a6577e580639945dcb28e4f3ee12443eadefe7 (byte-identical to pre-proof approval).
- SegreCoordinates.lean: 32a7e743d22711ac45d649b104faaf99417ac039389e8455049dc47e794ad04a.
- SegreNonzero.lean: b20f7cf0653882416e84c87b669766a66f2d89bc8fad585c6b5b7e8ccad83412.

The final sequential pinned Lean 4.33.1 rerun recompiled Definitions, Complexification, the unchanged boundary, and both new proof modules. All five exited zero; receipts and logs are evidence/015 through 019. All six statement theorems have transitive closure exactly propext, Classical.choice and Quot.sound, and each passes LeanCert #assert_trust kernel. There are no sorry/admit/custom axioms/native_decide or warnings in the final proofs. Earlier failing development logs are retained honestly and are superseded by the final successful logs; they are not successful verification evidence.

SEGRE-EVIDENCE.json records source and log hashes, exact commands and LEAN_PATH. Independent post-proof review remains required; this document is the implementer's evidence record. The prior FINAL-EVIDENCE.json for Complexification and ClosedFibers remains intact.

Formalization credit: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. Original TR-06 mathematical proof attribution: Matthew J. Colbrook. No contact email is included.
