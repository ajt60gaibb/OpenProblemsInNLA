# Independent review of root-authored Lean infrastructure

Date: 2026-09-12. Reviewer: Codex AI agent `/root/formal_review_standards`.
Reviewed baseline commit: `58bb28f99ea59a8b31a9162f800e2a0d29c0c889`, followed by the two fixes in the working tree. The final exact file hashes are below.

**Final verdict: approve the independently reviewed scope after both findings were fixed.**
This is an AI-agent review, not external human review. I authored the generic
harness and therefore do not count this as independent review of `harness.py`,
bootstrap/verify/selftest scripts, their source lock, notices or internal tests.
The independent scope here is the root-authored workflow, project discovery,
manifest validator, root tests and policy documentation.

## Findings, subsequently resolved

1. `tools/lean/validate_manifest.py`, YAML loading in `validate`: duplicate
   conflicting mapping keys are silently accepted by `yaml.safe_load`.
   I independently constructed a manifest beginning with `status.sorry_count:1`
   followed by a second otherwise valid `status` block reporting zero. The
   validator printed PASS. Reject duplicate YAML keys rather than choosing an
   interpretation of ambiguous public metadata. Reject duplicate Comparator
   JSON keys here as well; the separate harness already rejects them, but this
   metadata pass should not claim consistency for ambiguous configuration.
2. `tools/lean/projects.py`, `discover`: a registered `lean/` directory containing
   only `Challenge.lean` is invisible because none of the four marker files is
   present. I reproduced discovery and selection both returning an empty list,
   even when that problem's README was changed to `Lean verified`. Discover
   incomplete directories containing Lean sources (or any nonempty registered
   `lean/` directory), then let missing build/manifest requirements fail.

Resolution: I inspected the final duplicate-key loader and ordinary-directory
discovery changes and independently reran all 20 root tests. Duplicate top-level
and nested YAML keys and duplicate Comparator JSON keys now reject. Source-only
registered Lean directories are selected, and symlinked project directories reject.
Both findings are closed. The 20 root tests pass. The vendored JSON schema is byte-identical
to the pinned upstream v0.4 schema, SHA256
`25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce`.
The schema validator now correctly selects its declared draft via
`validator_for(schema)` and `check_schema`; the earlier hard-coded dialect
was fixed before this reviewed commit.

The policy documents preserve original target scope and permanent identifiers,
require statements and two reviews before implementation, distinguish
Comparator's formal identity check from informal fidelity, require kernel-only
LeanCert and actual transitive axiom evidence, retain source authorship, and
avoid claiming human peer review. Their per-problem PR/project design and
explicit incomplete status are appropriate. I found no material documentation
scope or attribution defect.

The workflow uses read-only repository permissions, pinned actions, no retained
checkout credential, a separate checker-controls job, non-root Linux with real
isolation prerequisites, per-project verification, and retained logs. It does
not substitute skipped project verification for a mathematical certificate.
Actual Linux execution remains a required gate; I did not run or independently
certify that workflow in this review. The two findings and their regression cases are resolved. Successful Linux
checker-controls are still required before claiming the shared infrastructure
operational.

| Independently reviewed file | SHA256 |
|---|---|
| `.github/workflows/lean-verification.yml` | `1cd1d8ce52125a9e26f1af4f6903c5f91c6a62385b527e372bd997f46e5d00a2` |
| `tools/lean/projects.py` | `d1aff2decea3af9af3f3062960119bc4f2924947742a2363083ab3b3834283d6` |
| `tools/lean/validate_manifest.py` | `31e473132c1e8a40c29f73eff01fbff0bafe85649da601d2f550cef164debeb1` |
| `tools/lean/requirements.txt` | `0b0709dc3105d98b29f4fc6a870c15c0cf42191498384ef8a2a32d3fcf5f34ed` |
| `tests/test_lean_verification.py` | `6c3795241e755d9b5f9c1c5aabed1666f72db26f38577e7f404a1edd42b57116` |
| `docs/lean/README.md` | `7c46e9abd0da85fef466d6529d7aba5768a9189c887ddb676d8bad42b52589a6` |
| `docs/lean/REVIEW.md` | `d967ddce620d4e754e2f9c25548f30cb537f76f4ddcf8ecf2574945bcd332553` |
| `docs/lean/schema/README.md` | `e61c5c99787b0c787dd197ff8713a56fa6b266070c92f7cdfb54b833755d53eb` |
| `docs/lean/schema/v0.4.schema.json` | `25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce` |
| `docs/lean/ci-toolchain/lakefile.toml` | `188b28d1f7649234f9c96a63e42c21469b023ddac1be5f257a51a75530ee16cc` |
| `docs/lean/ci-toolchain/lake-manifest.json` | `31fb5b12fe5424fc871b8f2508d2e1429d675d2512e3bdbfa0175e421f98e47f` |
| `docs/lean/ci-toolchain/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
