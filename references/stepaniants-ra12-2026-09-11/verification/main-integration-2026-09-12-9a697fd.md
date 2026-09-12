# RA-12: current-main integration with verification-level distinctions

Recorded 12 September 2026 UTC. This is a provenance-only integration, not a new proof review, literature search, status promotion, or workflow approval.

The preceding local head is `5b191a7318f29c418fa2920daff860ecbc501d35`, which already integrated accepted main `bfaa1d0675f24011e42740d48ea6966f83bb1bff`. The new incoming main is `9a697fdebee32be3003117700423bb81b1aab963`. The clean worktree merged these two parents without rewriting history or producing conflicts.

## Accepted content and mathematical scope

The RA-12 proof and its Solved canonical page were already accepted before this integration. The earlier [maintainer review and workflow observation](main-integration-2026-09-12-bfaa1d0.md) remain dated records. No new mathematical issue or change is asserted here, and no workflow execution approval was performed. Subsequent workflow status and pull-request acceptance remain maintainer actions.

All 217 canonical README files, the complete append-only registry, every canonical TeX/PDF and proof artifact, all accepted resolution records, and the incoming tools/tests are byte-for-byte identical to the new incoming main. This includes the accepted SP-11/SP-12 applications and the new distinction between informal independent review and Lean kernel verification. **RA-12 remains Solved; IE-01 retains the incoming Lean verified status.** This integration makes no Lean-verification claim for RA-12 or any other informally reviewed solution.

All six RA-12 canonical files remain byte-identical to both integration parents, including both PDFs. They were not rebuilt. The existing full-page PDF reviews apply to these exact retained bytes. All earlier RA-12 proof candidates, signed reviews, source/checkpoint hashes, network snapshots, integration records and checker scripts remain unchanged. The reference README retains the entire earlier text as a prefix and only appends a dated link to this note.

**Author:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. No personal contact email is added. Existing external theorem authors and Matthew J. Colbrook's earlier auxiliary counterexamples retain their accepted attribution.

## Checks

Permanent-ID validation and catalog generation pass against both `origin/main` (`ab754fabe3d48dc8d6eab6bcffce583e46d2b88f`) and the exact incoming main above. Regeneration leaves the incoming indexes byte-identical. All **17 permanent-ID tests** and all **3 status tests**, including Lean-verified handling, pass. The catalog retains **217 entries: 66 Open, 74 Partially resolved, 76 Solved and 1 Lean verified**. No ID was added, removed or changed by this integration.

The [machine-readable record](main-integration-2026-09-12-9a697fd.json) fingerprints every protected RA-12 file and the current integration files. The [read-only checker](verify_integration_9a697fd.py) compares every incoming tracked blob with its accepted version, permitting only the appended reference README; checks all canonical pages and ID mappings; verifies the accepted status counts, author affiliation and scoped absence of personal email; and preserves every older submission file.

Run at the recorded merge checkout with both parents available:

```text
python3 references/stepaniants-ra12-2026-09-11/verification/verify_integration_9a697fd.py
```

The two earlier integration checkers remain unchanged and should be run at their own recorded historical checkouts. Their old counts, metadata and renderer hashes are not relabeled as current evidence. No PDF was regenerated and no push, public post, workflow approval, or upstream merge was performed by the integrating agent.
