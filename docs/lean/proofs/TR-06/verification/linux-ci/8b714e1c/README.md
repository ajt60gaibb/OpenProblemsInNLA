# Actual failed TR-06 Linux push attempt

Exact source `8b714e1c4430c0c2bcd9cb5a98827d99375b89bb`; push run [40034425470](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/40034425470), target job `120690452247`. The workflow and target job failed. This directory is failure evidence, not Linux proof acceptance.

The unchanged snapshot guard rejected one accidentally tracked local cache symlink, `.lake/packages` (Git mode `120000`), before the project build. The artifact contains nine preliminary/control logs and no completed `result.json`. The cache symlink is outside the separately frozen 153 ordinary canonical inputs. The coordinating agent was informed to remove that Git entry without weakening the harness or changing mathematical inputs. A successful fresh exact-push receipt remains required.

The original GitHub artifact metadata, ZIP, exact extraction, run metadata and raw deterministically gzipped target-job log are retained. `FAILED_ATTEMPT_OBSERVATION_2026-10-23.json` checks their identities/digests and records the exact failure. Its passing observational controls do not claim any TR-06 Linux acceptance.
