# Independent proof review: weighted area contribution

Reviewer: /root/tr06_statement_referee_1, AI agent, nonauthor of this module or its area dependencies. Date: 2026-09-24. Phase: post-proof auxiliary-contribution review.

Verdict: APPROVE this contribution for integration. Reviewed source SHA256 `0c99df40f565920ffd0d3d3f205f090c956e63001b95bd9a8c661ff0b7cfbde6`. The approved pre-proof plan SHA256 is fac27f150b24cdc805725a1ec4d1d0800a38667c92f7b295b0041aaa1ac8b40b. The source was read in full and independently copied to source/NLA/TR06/WeightedArea.lean; it matches the current author bytes.

immersion_map_withDensity states exactly the proposed pushforward identity. For measurable t, map_apply is justified by globally measurable f, withDensity_apply needs only that the test preimage is measurable, and the area formula is applied to preimage(t) intersect s. All derivative, injectivity and measurable-set assumptions restrict correctly to this intersection. The exact set image identity gives the restricted target measure. There is no hidden Jacobian-measurability or finite-volume hypothesis in this result.

immersion_lintegral uses the explicit AEMeasurable density hypothesis for lintegral_withDensity_eq_lintegral_mul₀, and measurable w composed with measurable f for the other integrand. It keeps the exact rectangular normDet, the Euclidean-normalized Hausdorff measure in the domain dimension, the full image set, and ENNReal integrals. Infinite integrals and infinite-volume domains remain valid. Intermediate measurability assumptions have not been added to a frozen TR-06 final declaration.

Attribution retains Sébastien Gouëzel's Mathlib Jacobian credit, George Stepaniants with the requested Caltech affiliation, and Matthew J. Colbrook's original TR-06 proof; there is no contact email. The module imports the reviewed Area module and the ordinary lintegral-map API, never Challenge. No sorry, admit, custom axiom, native_decide, unsafe or custom elaborator appears.

Fresh reviewer rerun: recheck_weighted.py compiled the source with pinned Lean 4.33.1 into the same isolated review build whose Definitions and all six area dependencies had already been independently rebuilt. No author's proof olean was used. Exit 0, no warnings/errors. Both #print axioms closures are exactly [propext, Classical.choice, Quot.sound]; both #assert_trust kernel checks succeed. weighted-rerun.json records commands and environment. Full log logs/WeightedArea.log SHA256 `53ed34c4ac4a08eed16ad2a5683d86c141052cd6472862e912c1eb6aa92364ef`.

This is contribution-only approval. It is not Linux replay, Lean4 Comparator, a fresh dependency rebuild, graph-volume verification, or complete TR-06 approval/status promotion.
