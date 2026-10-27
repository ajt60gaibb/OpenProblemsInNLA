# IE-22 independent promotion review

**APPROVE the corrected metadata/status promotion at 53ddb09ee25f863f483a05f91b3f02ff1ad7b0d6. No remaining finding.**

Reviewer: AI agent /root/verification, 2026-10-26. I did not author the IE22 proof or promotion. This review concerns the exact metadata, original preservation, copied reviews, receipt references, permanent IDs and catalog change. My earlier immutable full-source/kernel approval remains separately scoped to 353ebcfc/57784643/06f31cdd. No Lean source or other agent's worktree was changed, and no new Lean, Comparator, sandbox or CI execution is claimed here.

## Inputs and results

The final snapshot was extracted directly from immutable Git objects into /private/tmp/nla-ie22-promotion-53ddb09e-verification-v2. It does not read a moving worktree for reviewed inputs. The reproducible driver and complete command logs are alongside this report.

- **114/114 independent checks pass**, including all 59 locked canonical package inputs, all 27 Lean sources byte-identical to the actually accepted 06f31cdd source, the 23 mathematical statement/proof copies identical to immutable 353ebcfc, and all 217 permanent IDs unchanged.
- **7/7 supplemental correction checks pass**: 799077c8 → 53ddb09e changes exactly tools/statement_inventory.py and generated COVERAGE.md, derives the scope-gap count from the actual collection, and leaves every one of the 59 canonical inputs and the retained original Linux receipt unchanged.
- All seven command groups pass: v0.4 manifest/Comparator coverage; all 45 statement metadata records; published-base permanent-ID guard; exact generated inventory check; eight existing inventory regression tests; the current author preservation driver; and an offline replay of the retained original Linux auditor.
- The preservation driver passes **271/271 static checks**. Seven independent README guard cases pass: original and exact promotion accepted; changed target, credit, date, status and historical suffix rejected. These are static guard tests, not additional proof or kernel claims.
- The offline original-Linux audit passes **220/220 checks**, preserving its actual head, executed merge, artifact and raw-log identity. This is a fresh local validation of retained actual evidence, not a new Linux run or a retrieval from GitHub during this review.

The original 6202 promotion had stale descriptive material. Commit 799077c8 removes the false claim that the live IE22 Target is an axiom and correctly scopes the preserved earlier author audit to its original prepromotion inputs. The corrected author README guard permits only the exact status/date replacement and the Lean evidence section, preserving all other original prefix and historical-suffix bytes. My additional finding that the generated prose still said six scope gaps was corrected at 53ddb09e; it now derives five from the actual collection. The statement and proof safeguards were not weakened.

The registry remains identical to the published base 01ed3c64648d2d8350ba80c4018894b6d785d2c9 and the earlier accepted/promoted trees. IE-22 retains linear-systems-and-elimination/IE-22/README.md and its exact mathematical target. The independent canonical-page count is **217 retained entries: 85 Lean verified, 33 Solved, 62 Partially resolved, 36 Open, one Solution claimed**. README/CATALOG counts and IE-22's unique retained catalog row agree. The source inventory checks only source coverage and is not presented as proof verification.

## Exact promotion and original preservation

All 59 package input hashes and lengths match PROMOTION_INPUT_LOCK.json and the immutable 6202 promotion package. They are also unchanged by the later 799 → 53 correction. All 27 Lean files, including Definitions, Challenge, Identity and Solution, are identical to the accepted 06f31cdd files. The Comparator still selects exactly:

1. NLA.Proofs.IE22.uniform_squared_upper
2. NLA.Proofs.IE22.near_sharp_unit_row_witness
3. NLA.Proofs.IE22.target

There are no replaceable definition names. The permitted axiom list is exactly propext, Classical.choice and Quot.sound. The live/frozen Target and actual full proof remain the already reviewed mathematical objects; the metadata does not promote the earlier lower-only checkpoint into a full proof.

The canonical README changes its exact status and last-checked date and replaces the Lean scaffold paragraph with a bounded evidence paragraph. Mechanically undoing those two preamble replacements yields the complete original preamble; the entire original suffix beginning at Problem statement remains byte-identical. Mathematical statements, references, source credits and dated historical audits therefore remain intact. The full original page is preserved both at IE-22/ORIGINAL.md and in the original statement archive. The 32 frozen original inputs and original scaffold text archive are checked again by the preservation driver.

The five new review Markdown files are verbatim copies of their retained campaign originals: both pre-proof reviews, the independent full-source inventory review, my full-source/kernel review, and the independent package review. Their exact hashes are recorded in result.json. The copies identify AI agents, retain their original source/checkpoint scope, and claim no external human endorsement. Original mathematical credit remains with Matthew J. Colbrook. Historical lower-only reviews retain their 7660eae8 limitations.

## Actual Linux receipt scope

The promoted README, formalization metadata and receipt refer to the authentic **original PR368 run 40255260833, job 121355717650**, at executed synthetic merge **88b9366e6cfcef7e60a2d740ff8a7101399bf1a8**, whose PR head is **06f31cdd4f76d90c7590b5582b8db4975a0055d8**. The receipt preserves its separate base/head/merge identities; they were not relabelled as the new promotion commit.

The original artifact is **12622124226**, 18,506 bytes, ZIP SHA-256 006c1919528d800bc18903d9f7f99633408cd0178f03d429bf57bd3489ef5468. Its decoded raw job is 106,057 UTF-8 bytes, SHA-256 d679fea63d8044b0051bdafa2b53ff004a063f7395b187605a191a4952730d27. The retained auditor revalidates the original ZIP/metadata/raw log, exact 54 original package inputs and 27 Lean files, generated exact consumer, all three actual exports, original kernel/standard-axiom reports and genuine rejection/sandbox/Comparator controls.

The 59-input promotion has five additional copied review documents and refreshed descriptive metadata, while its Lean bytes remain exact. Metadata explicitly says that the promotion receives fresh committed-project CI; the old 54-input receipt is not presented as an execution on this 59-input commit. A later reported 799-head Linux acceptance is outside this review and must retain its own independent receipt. No receipt for a new run was manufactured or inferred from this static assessment.

## Reproduction and limitations

Run review_promotion.py with the repository object store, immutable --commit 53ddb09ee25f863f483a05f91b3f02ff1ad7b0d6, a new empty --snapshot path, and an owned --output directory. It extracts immutable sources, runs the seven command groups, and emits result.json. Run check_correction.py separately for the exact final two-file delta. Python jsonschema 4.26.0 and PyYAML 6.0.3 were supplied by the existing /private/tmp/nla-oct23-pydeps installation.

The first reviewer snapshot omitted non-IE22 extra statement-review inputs, causing the all-statements guard to reject a missing AA-01 TeX file. The snapshot selection was corrected, all required immutable review inputs were included, and the complete final static review passed; the original failure is retained under attempts/incomplete-snapshot. A supplemental row check initially expected mixed-case badge text; it was corrected to the actual published uppercase LEAN VERIFIED badge, with its diagnostic retained under attempts/catalog-badge-case. Neither diagnostic was a package, theorem or safeguard defect, and no reviewed source was changed to make a check pass.

This approval certifies the stated metadata/preservation delta and retained-evidence correspondence. Proof truth rests on the separately retained independent source/kernel reviews and actual Linux evidence, with their exact original scopes. The overall campaign still has other Solved problems to address.

