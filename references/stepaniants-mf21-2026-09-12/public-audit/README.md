# MF-21 public-network eligibility check

The read-only check completed at **2026-09-12 03:37:45 UTC**. It recursively discovered 6 public repositories and 48 branch heads, read 232 distinct selected text blobs, scanned 175 issue/PR/comment bodies, and read 32 review bodies from 38 pull-request review endpoints. All six repositories have GitHub Discussions disabled.

Every returned MF-21 canonical page shows **Open**. All 48 heads share the canonical README Git blob 0a3237fec280661136874524680ca592030520f2. The only selected documents matching the exact problem/primary identifiers were that retained canonical statement, its rendered TeX, and catalogue entries. The wider Toeplitz/higher-order/expansion pattern found no alternate solution in the other selected text. No issue, PR, comment, or review matched the target patterns.

This is sufficient evidence of eligibility within this bounded public snapshot. It is not a claim about private, deleted, unpublished, unidentifiably named, or later-posted work. The mathematical review and source/literature check are separate.

The repositories were:

- ajt60gaibb/OpenProblemsInNLA
- MColbrook/OpenProblemsInNLA
- bonans/OpenProblemsInNLA
- k1monfared/OpenProblemsInNLA
- sgstepaniants/OpenProblemsInNLA
- yuningyang19/OpenProblemsInNLA

The portable helper audit_public.py was adapted from the preceding KE-05 helper with the target, canonical path, file selection, and search patterns changed to MF-21. All counts were rediscovered live. No cached immutable blobs were used in this run. It makes read-only GitHub API requests; it does not post or modify any public state.

The complete raw snapshot remains private at network-raw-private.json, SHA256
766360044ca1b5327045daf885b8af0e5e8932080d9516eac559abaaf89b590e.
**Do not archive or publish that raw file.**
The public-ready network-check-sanitized.json, SHA256
4720622fed1500e27165a85d19b59b6799814e6984b5adfb4d7f750e17522b9e,
retains repository/branch/commit identifiers, canonical path and status, document fingerprints, discovered counts, and the audit scope. Retrieved documents, bodies, identities, and contact information are omitted.

Reproduce with an authenticated GitHub CLI on PATH, or set GH to its executable:

    python3 audit_public.py --output /tmp/mf21-network-raw-private.json
    python3 build_sanitized.py --input /tmp/mf21-network-raw-private.json --output /tmp/mf21-network-check-sanitized.json

The sanitizer deliberately leaves the mathematical/eligibility assessment to this separate note; its retrieval counts are computed from the snapshot, not hardcoded.
