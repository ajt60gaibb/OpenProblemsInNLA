# TR-06 sampling-locus measurability proof

Author: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. Original TR-06 mathematical proof attribution remains Matthew J. Colbrook.

## Exact result

`NLA.TR06.measurableSet_identifiableRealSet (d : ℕ) (n : Fin d → ℕ) (r : ℕ)` proves `MeasurableSet (identifiableRealSet d n r)` with no hypotheses. The final set is the frozen definition, and the proof includes all natural-number and degenerate dimension/rank cases. The same file proves Borel measurability of the decomposable, exact-rank, and nonidentifiable loci.

Source: `NLA/TR06/Measurability.lean`, SHA-256 `f190029361743ded166300e47794424956bd55542aab744c50bc4ccd1b51a2a6`.

The route was independently approved before implementation; the exact statement/route and its hash are retained in `STATEMENT-PLAN.md` and `PRE-PROOF-APPROVAL.md`.

## Proof route

The raw factor parameter spaces are finite products of real coordinate spaces. The nonzero pure-summand domain is open. Its continuous tensor-sum image is sigma compact and Borel, with an explicit equivalence to actual `Decomposes` witnesses. Exact rank is this set minus every shorter decomposition set.

Pairs of nonzero factor tuples whose sums agree and whose tensor tuples disagree under every permutation form a locally closed parameter subset. Its tensor-sum image is sigma compact and Borel; the proof explicitly identifies this image with failure of the frozen `Identifiable` predicate. Subtracting it from the exact-rank locus proves the final statement. Sigma compactness, not an arbitrary Borel-image assertion, is used.

## Verification

Pinned Lean 4.33.1 exited 0 without warnings or errors. All four exported statements report only `propext`, `Classical.choice`, and `Quot.sound`; all four `#assert_trust kernel` commands passed using pinned LeanCert. The file imports immutable Definitions and never imports Challenge. No `sorry`, `admit`, custom axiom, `native_decide`, or target conclusion assumed as a hypothesis appears in the proof.

`evidence/Measurability.log` and `evidence/receipt.json` retain the actual final run and command, environment search paths, source hashes, permitted axioms, and scope. The scratch `check.py` reproduces compilation with available local package caches.

These are supporting-lemma results. They prove no genericity consequence, full-measure regular locus, dimension formula, induced-volume nullity, finite volume, finite angular mean, or full-target Comparator success.

## Original source preservation

Canonical target: [TR-06](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/tensor-computations/TR-06/README.md).
Original solution manuscript: [Matthew J. Colbrook, TR-06](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/references/colbrook-unclaimed-2026-09-11/manuscripts/TR-06.md).
The canonical original statement and original proof attribution have not been edited by this task.
