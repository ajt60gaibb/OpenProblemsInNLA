# Shared harness independent integration review

Date: 2026-09-12. Reviewer: OpenAI Codex AI agent `/root`.
The reviewer authored the workflow, project selector, metadata validator and
guide, but did not author `harness.py`, the shell entrypoints, source lock or
their test module. This report reviews that other agent's harness; it is not
an independent review of the reviewer's own infrastructure files.

Verdict: approve the scoped implementation, pending the actual Linux
operational run. This review verifies no NLA mathematical theorem and is not
a security certification or human peer review.

I read the full generic driver, entrypoints, provenance notice, usage guide,
source lock, and fetched immutable strict sandbox/probe source. The driver
selects the pinned Lean 4.33.1 compiler and hashes the actual built tools;
it rejects macOS/root authoritative use, mismatched tool receipts, unpinned
or non-public dependency locations, definition holes, duplicate JSON keys,
nonstandard permitted axioms, and identical Challenge/Solution environments.
The source lock records every fetched source byte, rather than fetching a
floating branch or substituting a historical Forsythe result for a new check.

The project snapshot comes directly from committed Git blobs, checks for
uncommitted tracked changes, rejects symlinks and build artifacts, and is
rechecked for input mutation after dependency/cache preparation and after
Comparator. Untracked local files cannot enter the copied proof. The
mathematical Solution is not built before Comparator in that fresh copy.
The real sandbox/probe and replay/Comparator controls precede the solution.
The explicit axiom allowlist excludes sorry, custom and native-execution
axioms, including Lean 4.33.1's generated native-decide axiom names. The
result record binds the selected declarations, source hashes, repository
commit and tool receipt. Failed commands cannot create a successful result.

The dependency preparation, Challenge definitions, Lake configuration,
compiler and checker remain trusted inputs that require their own source
review. The documentation correctly states these limits and separates formal
statement equality from informal semantic fidelity. The vendored strict
adapter supplies read-only outer mounts, a private build mount and private
process/network namespaces; the outer user service restricts AF_UNIX.
I inspected the actual positive and negative sandbox tests, including writes,
symlink escapes, host-process/network access and unexpected sandbox options.
Runtime success of those tests is required on the Linux verification host;
reading their source does not establish that a particular host enforces them.

I independently ran the 11 portable `test_harness.py` checks: all passed.
The separate agent's development build and replay observations were read as
reported evidence and are not represented here as independent Linux runs.
The new CI run must still demonstrate the actual pinned bootstrap, sandbox,
kernel replay and Comparator rejection controls. An operational failure
requires correction and rerun; this review cannot waive a failed gate.

Licenses and source roles are preserved in `tools/lean/NOTICE.md`. The
implementation follows the scoped Tau Ceti correctness, quality, reuse,
documentation, placement and attribution principles. It makes no assertion
of tool-author endorsement, external human review, or mathematical novelty.
