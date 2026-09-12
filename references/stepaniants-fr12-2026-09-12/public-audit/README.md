# FR-12 public fork, branch and discussion audit

Checked 12 September 2026 at 04:45:40 UTC, before publishing this submission. A [branch-head refresh](head-refresh.json) at 04:57:52 UTC found the same six repositories and 49 branch heads, with no added, changed or removed head and the same upstream main commit.

The [read-only retrieval script](audit_public.py) recursively discovered six public repositories in the network rooted at `ajt60gaibb/OpenProblemsInNLA` and enumerated every returned public branch. It inspected 49 heads, including the requested original repository and its public forks. The [sanitized snapshot](network-check.json) retains their exact names, commit hashes, canonical-file hashes, selected-document fingerprints, discussion URLs, counts, and retrieval scope.

There were 19 branch heads containing FR-12, all with `Open` status, and 30 without the page. The audit read 118 distinct selected text blobs. Selection covered canonical FR-12 files, root indexes, and Hadamard/doubling/matching/Ferber-named Markdown, TeX, Python and text documents. It also read issue and PR bodies and comments, review comments, and all returned PR-review bodies across the six repositories. The snapshot reports the exact discussion and review counts.

The sole matching discussion was [PR 111](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/111), which introduced FR-12 among 14 literature entries and retained it as an open counting problem. Reading its body and the selected documents found no competing resolution of FR-12. Upstream main was `1f22006bdaa4659fcaa0bb775a887685cd3cc566`.

This is a bounded public check, not a proof of novelty or a search of private, deleted, unpublished, unidentifiably named, or later work. Retrieved source texts and discussion bodies remain private. The [sanitizer](build_sanitized.py) removes their contents and contact data; only public repository metadata and fingerprints are archived here.

To reproduce, set `GH` to a GitHub CLI executable and run the retrieval script with `--output` pointing to a private scratch file, then pass that private file to the sanitizer using `--input` and a publishable path with `--output`. An optional `--cache-snapshot` reuses immutable Git blob contents by exact SHA only; live branch and discussion discovery still runs.
