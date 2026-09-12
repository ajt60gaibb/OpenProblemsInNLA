# PR127 recovery provenance and equivalence review

**PASS. The one metadata-label correction is fixed and independently rechecked.** Original reviewed head: `e5ad08c1a301d532ea200df8580224bb893b2240`. This is a bounded read-only review of the supplementary recovery material, not another audit of the complete central proof or PDFs.

Read `recovery/RECOVERY_NOTES.md`, the reconstructed `recovery/solution.md` matrix definitions, both supplied recovery checkers, `verification/verify_recovery_relation.py`, the comparison/report JSON, the submission README and canonical scope. All executed programs were inspected first and their outputs were directed outside the repository.

## Exact equivalence

The original perturbation zeros entry (8,2), while the reconstruction zeros (7,2). Let P swap rows 7 and 8, J negate column 7, and K equal I except K77=-1 and K78=1. Direct integer multiplication verifies L_recovered=P L_current K and M_recovered=P H_current J; both printed baseline matrices agree. The column squared norms match, so the normalized orthogonal factors satisfy Q_recovered=P Q_current J. Since J R K is triangular with positive diagonal when R is the positive-diagonal QR factor, the relation also respects the prescribed QR convention.

The comparison does not incorrectly assume row permutation preserves an arbitrary tied pivot path. It checks the specific first-available-row path at every stage. Through stage 7, the active matrices are related by the corresponding active row swap and column sign. At stage 7 their integer blocks are [[3063,2683],[-3063,2589]] and [[3063,2589],[-3063,2683]]. Both first pivots are legal, the final multiplier is -1, and the final integer pivot is 5272. Thus all eight normalized active maxima agree, despite different off-diagonal positions in the penultimate block.

Their common squared maxima are 3969/5272, 2209/1318, 29929/5272, 28561/1318, 56448/659, 450241/1318, 7198489/5272, 5272. The last is the largest; the common growth is exactly 5272/63.

## Reproduction and provenance

- The relation checker passes for the exact frozen source hashes.
- The supplied rational Gram-Schmidt/elimination checker and separately written block-inverse Schur-complement checker both pass.
- The regenerated certificate matches the supplied certificate byte-for-byte; the independent transcript also matches byte-for-byte.
- All seven raw recovery files match their manifest byte counts and SHA256 hashes.
- Recovery notes explicitly describe reconstructed material rather than an untouched historical archive. Their references to other recovery-session work are historical provenance, not extra canonical admissions in this PR. The submission README and comparison correctly count this as corroboration of the same IE-05 counterexample and do not assert independent human review or historical priority. Unobserved recovery events are not independently certified here.
- At the reviewed commit, the 203 ID/path pairs equal its published base `87366c62d3b5c47d170f747b1cb40ab38d501013`. IE-05 is the sole changed canonical README. Its entire text from Context and notation onward is byte-identical to that base, preserving the exact target and preceding source/status history. The recovery addition creates no new target or solved count.

## Metadata correction identified

The relation checker/JSON field `positive_QR_upper_diagonals_identical` contains diag(T) from H=L T, rather than the QR R diagonal. For example its first entry is 1, while R11=sqrt(8). This does not invalidate any assertion or equivalence calculation: the true QR diagonal is sqrt(D_ii)/T_ii and agrees for both inputs. The integrating agent renamed the field to `positive_integer_upper_factor_diagonals_identical` and refreshed both entries in the current artifact manifest, with an explicit correction record. Independent final comparison verifies that the script changes only this string, the JSON changes only this key, both new fingerprints match, and every historical manifest/raw recovery file remains byte-identical. The corrected checker rerun passes and reproduces the corrected JSON byte-for-byte. Final correction evidence: `PR127-recovery-final-correction.json`. No blocker remains.

Evidence: `PR127-recovery-checks.json`, `PR127-recovery-relation-rerun.json`, `PR127-certificate.json`, `PR127-independent-rerun.txt`. Central mathematical proof, PDF QA, final main integration and CI are assigned to other agents.
