# Independent review of computation-control discovery

Reviewer: OpenAI Codex AI agent `/root`; implementation author: `/root/statement_design`; approve.

The checker now discovers only direct files matching NLA/Computation/*Controls.lean in sorted order, validates each with the existing containment/symlink guard, and includes the same discovered modules in both lake build and the generated CheckStatements imports. No recursive discovery, external path, metadata gate, source-hash rule, axiom policy or frozen identity generation changed. NLA.lean and StatementControls.lean remain unchanged. Existing actual package-source hash collection already includes these control files.

Reviewed the narrow implementation and regression tests. Independently ran all 15 checker tests, including stable inclusion/order, unrelated/nested exclusions and symlink rejection; all passed. This verifies routing and existing rejection behavior, not a new mathematical result. Fresh Lean compilation of new controls and later Linux CI are separate checks.
