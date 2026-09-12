# PR 153 independent maintainer audit

PR: <https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/153>  
Original reviewed head: `eaf3b80698555171804bef29e3a9e2b1607bc875`  
Integration base: `d7fcfe7bfe8c02cd98d9463fa5a8ba12850d5bdb`  
Repair commit: `82a55c4`  
Main integration commit: `e17424d8e6104667c97d76e81ce52384368b310c`

**Disposition: PASS for the repaired source and local integration; merge remains conditional on fresh final-head CI.**

This audit independently examines the new Lean verification infrastructure. It does not certify a mathematical theorem or promote a problem status. The submitted AI reports were read as claims to check, not accepted as evidence of correctness.

## Findings and integration

The original selector could silently skip verification after removal or relocation of an entire registered Lean project. It also missed Git-quoted Unicode and quote-containing filenames. The shared-tool workflow detector had the same pathname problem and could miss the old side of a rename. The repair compares registered projects with the base tree before producing a matrix and uses NUL-delimited, rename-disabled diffs. Real Git regression tests cover deletion, relocation, partial deletion, both sides of file moves, newly added source-only projects, and Unicode, quote and newline filenames. The root reviewer independently read and approved the subagent's patch.

Documentation now states the retained-project rule, qualifies the contributor-specific attribution instruction, and accurately explains that read-only filesystem access is not host-file confidentiality. Authoritative runs require an isolated, credential-free Linux runner.

All 217 registered canonical pages, their original mathematical targets and statuses, the ID registry, the catalog and other published indexes, and existing TeX/PDF artifacts are byte-identical to the integration base. The only changed pre-existing main file is the four-line CONTRIBUTING pointer. The recent main changes in PRs 151 and 152 are preserved. The submitted historical Linux evidence is unchanged.

## Independent checks

- Permanent-ID validation passed against the integration base; catalog generation reports 217 entries: Lean verified 2, Open 57, Partially resolved 71, Solved 87.
- All 17 mandatory permanent-ID tests passed.
- The complete repository unittest run passed 68 tests. Its separate Pandoc-dependent class was skipped because Pandoc is absent locally; those rendering inputs and tests are unchanged from main.
- All 12 harness tests passed. The repository total above includes all 30 selection/metadata tests, including the repaired cases.
- Separate metadata/path probes matched all 11 expected results.
- The provenance reviewer checked all 58 pinned sources, all 35 retained evidence-manifest entries, every original ZIP member, and live GitHub job/artifact correspondence. The archived run covers checker fixtures and has an empty, skipped per-problem matrix; it is not an NLA theorem verification.

The portable checks used a dedicated temporary virtual environment with the PR's pinned PyYAML 6.0.3 and jsonschema 4.26.0. No authoritative Linux verification was claimed on the local macOS host.

The workflow has no stable aggregate required check. Before merging this revision, the maintainer must observe successful permanent-ID, select, and applicable checker-controls jobs on the exact final head. A skipped empty per-problem matrix is expected for this infrastructure-only PR. Historical green results do not satisfy this final-head gate.

## Reports and evidence

- [Workflow and metadata review](workflow-review.md) records the original FAIL, reproductions, repairs, and limits.
- [Provenance and documentation review](evidence-review.md) verifies the retained Linux evidence against live primary records.
- [Harness source review](harness-review.md) and [native-reduction review](native-reduction-review.md) resolve the questioned pathway for the pinned version. Both independent reviewers and the root reviewer traced the empty IR state, mandatory interpreter lookup and propagated rejection; the source review passes under its stated trust model.
- [Integration identity](integration-integrity.json) and the retained command logs record local validation.

The Git commit containing this report binds its source files. The final CI run and merge receipt are recorded separately after this commit exists, avoiding a circular claim that a report already contains its own final commit hash.
