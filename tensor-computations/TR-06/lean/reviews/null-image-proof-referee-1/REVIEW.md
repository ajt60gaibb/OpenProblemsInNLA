# Independent contribution review: C1 null-image transfer

Reviewer: /root/tr06_statement_referee_1, AI agent, nonauthor. Date: 2026-09-24. Post-proof contribution review after my pre-proof approval of NullImageBoundary SHA256 62ab72803696d403e953228937b055148968446527449485067ca714bb77a4fd.

**Verdict: APPROVE for integration.** Source NLA/TR06/NullImage.lean SHA256 e35fd011d6e56bed64b472ce1240f3db38743a241f2e27d8e4c4befa66b96265. I read the entire source and independently rebuilt its snapshot under source/ with the previously reviewer-rebuilt Rectangular dependency tree. No author-produced proof olean was used.

contDiff_image_null has exactly the approved supporting assumptions: finite-dimensional real Hilbert source/target with Borel structures, global C1 map, and arbitrary volume-null source set. The target Hausdorff exponent is the source finrank. There is no injectivity, source-set measurability, positive dimension, compactness of the whole set, or target-measure nullity premise.

For each integer-radius closed source ball, compactness and convexity justify the pinned C1 Lipschitz theorem. The arbitrary intersection with s is volume-null by monotonicity. The exact Euclidean Hausdorff normalization converts that to source-dimensional μHE-nullity, and the reviewed Lipschitz image bound gives null image. Finite NNReal Lipschitz constants remain finite after power, although the proof only needs multiplication by zero in ENNReal. The countable closed-ball exhaustion is exact and measure_iUnion_null requires no measurability of the images. This handles nonmeasurable outer-null sets and source dimension zero. The local unused-section-variable linter option preserves the reviewed interface without changing trust.

The source correctly credits George Stepaniants and the requested Caltech department affiliation, with no email, and preserves Matthew J. Colbrook's original TR-06 proof attribution. No sorry, admit, custom axiom, native_decide or Challenge dependency appears. It proves only null-image transfer; nonzero polynomial pullbacks in the correct Segre dimension remain separate.

Independent pinned Lean 4.33.1 rerun exit 0, no warnings/errors. Printed axiom closure is exactly [propext, Classical.choice, Quot.sound] and #assert_trust kernel passes. null-image-rerun.json records command/environment/source and log hashes. Full log logs/NullImage.log SHA256 4f42c938d818b995cdf35dc401822e40b19a1c46c51d20f2b678af37e7012115.

This is contribution-only approval, not fresh dependency rebuilds, Linux replay, Lean4 Comparator, complete regular-locus proof or TR-06 promotion.
