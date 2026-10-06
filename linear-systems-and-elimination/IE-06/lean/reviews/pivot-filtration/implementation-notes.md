# Canonical pivot filtration: author implementation record

This records implementation of the independently preapproved `../pivot-filtration-specification.md`, including its approved entire-future-block extension. It is not an independent review of the author’s own code.

The actual finite ascending comparison scan is Borel measurable. The exact recursive selected trajectory and path are therefore measurable, as is the selected left elimination operator. Inputs agreeing on original columns j<k yield the same first k completed pivots and the same selected operator at stage k. The operator factors through the original matrix with later columns zeroed; no nonzero pivot or nonsingularity hypothesis is needed for these totalized deterministic statements. The next pivot at stage k is not claimed to depend on only the first k columns.

The concrete nested Gaussian law is rearranged into columns using the proved flat-entry law and an exact coordinate permutation. Its columns are mutually independent standard Gaussian vectors. Applying finite independence to disjoint past/future column sets, then the proved measurable selected-operator factorization, gives the exact joint law of the selected operator and every future column, and separately the entire future block. The joint laws are products of the actual selected-operator marginal with the actual Gaussian vector/block law. This is joint freshness, not merely pairwise independence. Empty blocks and zero dimensions are included.

No global successful event is conditioned on, no selector is left unspecified, and no union-bound penalty appears. All declarations are new proofs over the credited Pivot and Elimination definitions, using pinned Mathlib’s measurable product and independence theorems. There is no copied untrusted stochastic estimate or assumption of the main result.

All 29 local definitions/theorems passed LeanCert kernel trust assertions; all printed axioms are the standard three. The attached receipt binds source, compiler and output hashes. Root independent review and complete immutable package verification are separate from this trusted-cache local compile.
