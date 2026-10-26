# Canonical solved-proof inventory, 23 October 2026

Independent source audit by AI agent `/root/inventory`. This report does not
claim a fresh Lean, LeanCert, Comparator or CI verification. It reads immutable
Git objects, preserves all canonical paths and original targets, and writes only
this report directory. Pre-existing dirty files are untouched.

Published main is now `5487945e5a72abd952b0c89915915de8cc9b3e65`, the 18 October
merge of PR #361. The coordinator verified the current GitHub main SHA and
fetched it. The earlier 17 October report was frozen at `47006df8`; that report
must not be used as the current proof inventory. All 217 registered ID/path
pairs are identical between those two published commits.

Reproduce the fixed published and candidate source hashes with:

```bash
python3 reviews/2026-10-23-solved-lean/inventory/generate_inventory.py
```

| Canonical status | Count |
| --- | ---: |
| Lean verified | 80 |
| Solved | 38 |
| Partially resolved | 62 |
| Open | 36 |
| Solution claimed | 1 |

The 38 Solved entries are the actual outstanding full-target campaign, not the
56 Solved entries in the stale dirty checkout. Eight have incomplete live proof
projects on published main; 30 have only reviewed statements and informal proof
sources there. A Target definition, `#assert_statement`, kernel trust of a
definition, a Challenge hole, or a proof conditional on the missing mathematical
gate is not a proof of that Target.

## Completed work to reuse

The formerly-Solved proof campaign now has nine promoted full targets: FR-05,
TR-13, MF-23, RA-06, MF-03, RA-10, MD-03, MD-04 and SP-11. Their proof source and
existing receipts are indexed by published `docs/lean/proofs/INVENTORY.md`.

In particular, SP-11 is **already Lean verified**, not pending a new full proof.
Its `docs/lean/proofs/SP-11/LINUX_CI_RECEIPT.md` records full-target Linux run
39131755109, job 117688269984, artifact 12138590670, and immutable checked commit
`9264361fafb89b37b5c48236afebb304bc84110a`. The existing actual-artifact audit
records Comparator acceptance, LeanCert kernel proof trust, all 135 committed
project inputs, 40 artifact checks, and only `propext`, `Classical.choice` and
`Quot.sound`. This inventory inspected the receipt and theorem source without
replaying that artifact. Between the checked commit and current published main,
the SP-11 canonical project differs only in README.md and formalization.yaml;
the proof and frozen statement bytes are unchanged. The receipt correctly
distinguishes those metadata changes from its original checked input hashes.
The old SP-11 packaging plan is a retained historical draft.

## Exact remaining IDs

Incomplete live projects on published main (8):

IE-21, IE-22, IV-02, IV-04, MD-06, TR-04, TR-14, SP-14.

Reviewed statement/informal proof only on published main (30):

AA-01, AV-01, AV-02, FR-10, IE-08, IE-10, IE-12, IV-05, MF-08, MI-16, NM-03,
PF-04, PF-05, RA-04, RA-05, RA-12, RA-13, RE-05, RE-06, SP-12, TR-06, TR-08,
TR-17, TR-20, TR-21, TR-26, IE-26, MI-31, RA-19, SP-13.

## Existing unmerged development

These candidates must be reused or reviewed before starting duplicate work.
The machine-readable inventory includes immutable SHAs and every live source
hash. Source counts below include statements/Challenge/definitions where
present, and are not counts of complete proofs.

| ID | Candidate commit | Actual implementation and remaining gap |
| --- | --- | --- |
| TR-14 | `fdb40b66425ec58e4806cee93d2aaf92a0f8597c` | 39 shared Lean modules. Adds binary top-remainder/Frobenius/representer/moment-unit work to the published chart, apolarity and local CRT/Fourier upper-width route. The other symmetric upper construction and the general lower bound for arbitrary ordinary decompositions remain. Neither a normalized-chart upper bound nor middle-catalecticant rank proves the all-width ordinary/symmetric equivalence. |
| PF-05 | `6e2c960557b6f61af1ed6e679b0634dd498181b2` | Seven finite-matrix support modules plus five statement/check files. Rank-three factorization/operator/congruence and zero-pair normalization work exists. No Solution.lean. The positive-entry infinitesimal-rigidity/topological theorem, full zero-case feasible direction/integration, and complete assembly remain. The positive case cannot be imported informally or assumed as an axiom. |
| TR-06 | `50e97f90c11a65028500cb1dcd840c1de0bb314b` | 59 live files: frozen Definitions, Challenge, and 57 support/definition/audit modules. Five of ten Challenge declarations have separate locally checked implementations. Actual generic regularity and exceptional-locus nullity, normalized graph volume, polar integration, normalization and full finite-mean/source-model correspondence remain. No Solution.lean, no completed target or Linux Comparator result. This substantial older branch was absent from the prior candidate table. |
| RA-19 | `0b5ac28a922c8c8768dfe043a6e282cd190bcfe8` | Exact independently reviewed contract only; no live Lean proof module. Uniform nonempty polynomial-open witness, reduced normal-bundle/resultant multiplicities and the critical-point bijection remain. |

TR-14 and PF-05 are the most developed finite-algebra routes among inspected
unmerged candidates, but neither is merely awaiting packaging or CI. TR-06 has
the largest separate foundation development and several substantial geometry
and measure-theory gates. SP-12 is not an immediate corollary of the unrestricted
SP-11 matrix theorem: its positive-semidefinite SAP invariant and chromatic
conclusion need their own reviewed proof. SP-13 requires the dimension-free
weak-type triangular-truncation argument and full spectral-distribution limit.
No remaining full target was found that should be advertised as a short numeric
certificate exercise.

The old partial canonical projects also require semantic repair in some cases:
IE-21/IE-22 retain a full-target axiom and incomplete row-law semantics;
IV-02/IV-04 lack the exact complexity semantics; MD-06 assumes abstract event
semantics; TR-04 leaves rank/operation-count semantics unconstrained. SP-14's
large finite Fourier/jet development still lacks the stagewise packet control,
compatible inverse, final infinite symbol, nonextension and unconditional
subsequence gap. These are actual mathematical gates, not evidence-generation
tasks.
