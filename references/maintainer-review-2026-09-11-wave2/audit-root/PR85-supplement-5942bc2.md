# PR85 supplement: upstream integration at 5942bc2

Reviewed head: `5942bc2274df99b10cd26b62df07ff822dffee69`, a merge of the previously reviewed `6fb1041e83823f726a326b33ef8169cd593df631` and published main `16369809e6e600144bd350ab70b7473b652f46f1`.

**Mathematical verdict: PASS carries unchanged. Documentary verdict: the historical-hash finding is still unfixed, and two current-file fingerprints became stale during the upstream merge.**

I compared the head directly against its published-main parent, then compared its contributed files against the previously reviewed head. The genuine PR delta contains the same 18 originally contributed paths plus the already-reviewed optional-email template change. The merged upstream's other resolutions are retained: all 202 canonical problem pages other than MI-28 are byte-identical to main. All 203 permanent ID/path pairs are byte-identical, and MI-28's original problem-statement section is byte-identical. Its complete canonical README, proof Markdown/TeX/PDF, canonical problem TeX/PDF, original manuscripts, discovery note and prior review are unchanged from `6fb1041`. The previous five-page PDF visual inspection therefore remains applicable; no redundant rerender was needed.

The only renderer difference from published main is adding MI-28 to the reference-page-break list. The safeguard code, tests and numbering workflow are unchanged. Direct counting of all 203 canonical statuses agrees with the regenerated catalog: 77 Open, 76 Partially resolved, 49 Solved, and 1 Solution claimed. The top-level and category catalog differences only move MI-28 to Solved and update the corresponding counts; the new RESOLVED entry states the already-reviewed full positive-definite target.

The remaining corrections are all in `references/stepaniants-mi28-2026-09-11/verification/document-checks.json`:

| Line | Field | Correct SHA-256 |
| --- | --- | --- |
| 71 | Current `files` entry for `tools/render_problems.py` | `d4e7ef4c1db0e8c60b3a7f7fd67cbf63611c2a5a3ea15d03d6327ac572f9bc3e` |
| 73 | Current `files` entry for `references/stepaniants-mi28-2026-09-11/README.md` | `8ed7f793bf545f0bf2d6d0a91f8854896c07d6bf89e5b5520e4c24d4f9db98c5` |
| 93 | Historical `pre_email_redaction_record.pdfs[0].sha256` | `f225b707eef5a0684b705f3b6a02d1fc083a1cbd4842439d19695172ef0b2be5` |

Keep the top-level current solution-PDF digest unchanged. Keep the historical renderer fingerprint unchanged within the historical record; only its top-level current fingerprint is stale.

`check_PR85_merge_delta.py` uses read-only Git object reads from a separate temporary clone. Its `PR85-merge-5942bc2-evidence.json` records **35/38 passing checks**, retaining the three fingerprint findings explicitly. No mathematical or permanent-target check failed. No shared index, branch, snapshot or workflow was changed, and no GitHub workflow was approved. This is analytic agent review, not proof-assistant certification.
