# Status and exact target correspondence

## Original RA-05 entry

**Proposed whole-entry status: PARTIAL / Partially resolved, subject to review.**

The canonical question fixes an arbitrary real p > 2 and asks for the optimal
joint dependence on k and epsilon, up to logarithmic factors, for arbitrary
input matrices and nonnegative coresets supported on original rows. This
package does not establish that full all-exponent classification.

The status recommendation is about incomplete mathematical scope, not merely
about the absence of independent review. The repository distinguishes partial
results from complete claimed resolutions and from independently audited or
formally verified complete results; see the source in `SOURCES.md`.

## Completed scope reported by this manuscript

Theorem 1.1 supplies matching upper and lower orders, up to at most a ninth
power of log(2k/epsilon), for **p = 4**, every k >= 1, every 0 < epsilon < 1/2,
and arbitrary input rank, n, and d. All upper-bound weights are nonnegative and
select original rows. Queries are all subspaces of dimension at most k.

The proof of the new second upper branch is in Sections 2–7. Both lower
constructions and their combination are in Section 8. Zero optimum, singular
feature metrics, ambient-row-span compression, and composition of positive
row weights are addressed explicitly.

This is a complete mathematical argument for that fixed-exponent subtarget,
not a claim of publication, independent audit, or formal verification. The
archive does not change the repository's status or submit a pull request.

## Preceding work

The unchanged preceding package contains the earlier counterexamples to the
proposed inequality and restricted even-power classification. Those results
are not silently renamed complete all-exponent solutions. The new quartic
lower bounds are proved again, so the present theorem does not need the
archived principal asymptotic statements as premises.

## Evidence level

- Author-side proof and source audit: supplied in PROOF_AUDIT.md.
- Reproducible finite checks: 7,621 assertions plus separate exact checkers.
- Independent review or peer review: not performed or claimed.
- Proof-assistant/kernel verification: not performed or claimed.
- Priority/novelty certification: not performed or claimed.

No canonical problem statement, input quantifier, or original-row restriction
has been weakened in the stated p = 4 theorem.
