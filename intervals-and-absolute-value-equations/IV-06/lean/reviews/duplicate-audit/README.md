# IV-06 public duplicate-formalization audit

Observed on 12 September 2026, with raw query timestamps in the receipts. The upstream repository was `ajt60gaibb/OpenProblemsInNLA`, at `f41f1f9ffa2171550d4bb795862c6170c4f26070` on its observed main branch. The canonical IV-06 page is already **Solved** by Colbrook's informal counterexample; this search concerns a duplicate Lean verification track.

The GitHub API returned seven public forks. Branch lists for upstream and all seven forks contained **83 heads representing 72 distinct commits**. Branch counts were upstream 10, `mattman059` 1, `sidneyholden1` 11, `yuningyang19` 5, `sgstepaniants` 37, `k1monfared` 1, `MColbrook` 16, and `bonans` 2. All paginated query calls completed successfully.

Seventy-one distinct commits were available as exact local Git objects and their full recursive path lists were inspected. One missing local commit, `5484ec05eb8adf4a0da9968c45d22629727d4ac9`, was inspected through an actual untruncated recursive GitHub tree response containing 2,671 blob paths. The case-insensitive path check looked for `IV-06` or `IV06` together with Lean source, `formalization.yaml`, or a `lean/` path. **No matching IV-06 formalization path was found in any of these 72 observed trees.**

All **63 returned upstream PRs**, and all fork PR lists (each empty), were checked for IV-06 identifiers in titles, bodies and head names. The only match was [PR 62](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/62), merged on 11 September 2026: the existing informal interval and absolute-value resolutions by Matthew J. Colbrook. No matching Lean PR was found.

[original-receipts.zip](original-receipts.zip) contains byte-identical raw GitHub metadata, branch/PR pages, every local tree list, the remaining actual API tree, and machine-readable results. [receipts-manifest.json](receipts-manifest.json) binds every uncompressed file and the original archive itself with byte counts and SHA-256 hashes. The archive was reopened and every entry rehashed after creation.

This establishes only the inspected public branch/PR scope at the recorded time. It does not cover deleted or private branches, future changes, unpublished work, or a formalization hidden under unrelated identifiers. It is not a historical-priority determination. No remote repository was changed by this audit.
