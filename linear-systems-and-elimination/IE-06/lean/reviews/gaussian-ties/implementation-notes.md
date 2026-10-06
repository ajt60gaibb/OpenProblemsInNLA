# Gaussian pivot tie proof: author implementation record

This records implementation of the independently approved `../gaussian-ties-specification.md`; it is not a claim of independent review of the author’s own code.

`GaussianTies.lean` proves that under the actual `gaussianMatrix n` law all admissible paths are almost surely unique and agree with `firstPath`, including the zero-dimensional case. Fixed finite path trajectories are represented by rational functions with a common polynomial denominator. A backward realization lemma with unit prefix pivots proves that the squared-magnitude difference polynomial of two distinct active entries is nonzero whenever the prescribed prefix is active. Admissibility implies both activity and nonzero denominators. The actual Gaussian polynomial-null theorem then gives almost-sure simultaneous separation for every finite path, stage and distinct row pair. A deterministic induction gives path uniqueness, and Gaussian nonsingularity plus proved GEPP give existence.

The activity hypothesis in the polynomial nonvanishing theorem is essential and explicit. The realization permits singular trailing blocks. No independence of adaptive Schur entries is assumed; no union bound with a positive factorial cost is introduced.

This is a new algebraic proof of the source’s probability-zero tie claim, using the existing credited exact IE-06 GEPP definitions and the independently reviewed GaussianNull polynomial theorem. It does not import or assume the main manuscript theorem or any probabilistic growth estimate.

The accompanying compile log passes all twelve `#assert_trust kernel` checks; each theorem’s printed axiom set is contained in the standard three axioms. The receipt binds the source, compiler and output hashes. This local compilation uses pinned trusted dependency caches and is not a claim of independent Linux Comparator replay. Root review and whole-package verification are separate.
