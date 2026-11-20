# Independent quasi-finite character-bound contribution review

Reviewer: /root, nonauthor of these two modules; author of the separately independently reviewed AlgebraFiber dependency.

APPROVE QuasiFiniteCharacters.lean SHA256 `5883a702181173166ee476b9f0694e338003e858158ad8c5a00f674918a158f1`, with definitions SHA256 `90fbd3a5d72f961aa31b5e3198c851e3e81aa1034141bdfaca05ea49e995457a` exactly matching the root-approved pre-proof boundary.

I read the whole implementation. The local restriction proof correctly applies the away-map denominator identity to arbitrary s, then uses equality of restrictions and the nonzero common denominator to cancel in the field. Only one nonzero-denominator hypothesis is used because equality of restrictions supplies the other.

For each actual quasi-finite prime, Zariski Main produces a finite module envelope and a principal source open. Every subset of Noetherian Spec(S) is compact, so the quasi-finite subset admits a finite subcover without any unstated openness premise. Generating families and their finite sum B are chosen before the R-algebra action on K. Each filtered character set injects into envelope characters and is bounded by the finite-generator Artin-independence lemma, which needs no freeness. The actual kernel condition puts every character in some chosen open; finite-union cardinality then gives the exact global conclusion. Empty loci and empty finite subsets require no extra assumptions.

Independent rerun of copied source completed with exit0, no warnings, permitted closures exactly propext, Classical.choice, Quot.sound, and kernel assertions for both exports. Receipt and log retained alongside this review. Dependencies were pinned prebuilt artifacts, and AlgebraFiber was root-authored and separately reviewed.

This proves only the explicit algebraic character bound. Actual tensor graph representation and quasi-finiteness at its regular projection points remain unproved. This is not a complete-target or Linux Comparator verification.
