# Exact retained ten-declaration TR-06 boundary

23 October 2026. Author scope report by campaign recovery/geometry agent.
`RetainedBoundaryLocus.lean` and `RetainedBoundaryMean.lean` prove all five
formerly pending declarations of the published TR-06 Challenge. Their
original names and types are preserved under `NLA.TR06`; the other five names
remain in the unchanged retained proof sources. The new source lock is
`retained-boundary-source-lock-2026-10-23.json`.

`regular_locus` derives measurable loci and their inclusion from the actual
model. The proved generic full-measure smooth locus implies the stated
regular-locus exceptional set is null. Positive actual annular Hausdorff
volume, with the expected intrinsic dimension, implies the regular measure
of the whole space is nonzero. No positive-mass assumption is supplied by the
caller.

`smooth_locus_correspondence` uses the exact principal/source genericity
equivalence, the actual generic full-measure theorem, and the frozen source
and regular volume restoration equalities. `source_model_correspondence`
uses the proved Gaussian-normalizer and input-law equalities, followed by
the actual almost-everywhere angular equality under that same source volume.
Neither theorem assumes equality of the loci at every exceptional point.

The two mean declarations use the separate literal intrinsic theorem
`NLA.Proofs.TR06.target`. `Model.generic_iff` transfers the original genericity
hypothesis. Under the proved actual full-measure smooth locus, the frozen
normalizer and angular-integral equalities identify the intrinsic quantities
with the retained metric model, while the proved normalized integral formula
identifies its actual expectation. The positive finite normalizer gives an
actual probability measure. The source-law and source-angular restoration
then give the complete original source target. No finite-mean, finite-volume,
or geometric certificate is added to either original theorem's hypotheses.
`Final.lean` does not import these boundary wrappers, so this transport is
acyclic.

Both new sources compiled with their kernel assertions, and their printed
main-theorem axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
The actual author build log is retained in the persistent recovery evidence
under `geometry/retained-boundary-author-build.log`. This is author evidence,
not independent approval or Linux/Comparator evidence.

The separate `retained-boundary-original-types-2026-10-23/Consumer.lean` is
generated directly from the authoritative published Challenge at commit
`3da7a876b97815c99ebde0f4f9c17932096345a2`. Every one of its ten original
binder/type headers is copied verbatim; only declaration names and proof
bodies differ. It applies the actual completed proof to each exact original
type. Its corrected execution passed all ten kernel assertions, with only
the standard three axioms. Source provenance, actual command, compiler
version, logs, hashes, and output-object hash are retained with its result.
The first invocation's working-directory error is separately retained as a
failed driver invocation and is not counted as a mathematical check.

The independent full-source audit and the separate canonical Challenge,
Comparator, and exact-commit Linux artifacts remain distinct gates. This
report does not itself change the canonical problem status, problem ID,
original target, original README, or archived mathematical artifacts.
