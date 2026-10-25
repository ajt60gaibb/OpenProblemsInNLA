# TR-06 final immutable package acceptance

**PASS: the full unchanged intrinsic Target and all ten original published theorem types.** Final source `ba78bccb76fe219b7686cab9bca61b845636ad7a` has 153 frozen inputs, 144 Lean sources, 140 exact source copies (80 completion proofs, 58 retained originals and 2 statement sources), and 11 selected theorem exports. Metadata phase is `complete-proof-linux-verified`; canonical status is Lean verified. The broader all-Solved campaign remains active.

[Actual final push run 40050555644](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/40050555644), [TR-06 job 120742137176](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/40050555644/job/120742137176), artifact 12543188710. Original ZIP SHA-256: `6ccc6bb5e43b1677c5e4ff9100b8039a4480a6d9aaec8e5c9e4afb0ef2212a71`. Both root and independent strict replays pass 45/45 controls against all 153 inputs. All 11 selected exports are actual theorem constants accepted by LeanCert kernel mode and Comparator's default kernel, with only `propext`, `Classical.choice` and `Quot.sound`. Actual rejection, sandbox and regression logs are retained. The PR synthetic merge is separate and supplies no evidence here.

`FINAL_ACCEPTANCE_2026-10-24.json` binds the complete three-stage actual acceptance chain: proof `2b049df5`, descriptive promotion `5a9f6eef`, and final metadata ba78bccb. Each has separate root/independent strict 45 receipts and its original artifact. Every 144 Lean input byte is identical across all three stages. Promotion changes only package README/YAML; finalization changes only the three approved YAML values. The 24 final checks also bind the fresh shared/canonical audits, all 217 permanent IDs, all 216 other unchanged pages, exact recoverability of the original TR-06 page and all five original archives. Earlier cache-symlink failure `8b714e1c` is retained explicitly as failure; the harness was not weakened.

Actual final push boundary run 40050555619 and ID run 40050555607 also passed. Original statement/identity artifact ZIPs, three raw logs and a separate twelve-control observation are in `boundary-and-IDs/`. Their scope remains distinct from the full Target receipt. All original mathematical/formalization credit remains preserved; completion and reviews are AI-agent work, with no external human endorsement claimed.

The filename date 2026-10-24 identifies this receipt batch. `root-replay-execution-2026-10-25.json` records the later actual root replay; the final acceptance records its actual UTC execution time. Raw reports are never relabeled as an earlier execution.

Reproduce the complete retained chain from the repository root:

```sh
python3 docs/lean/proofs/TR-06/verification/final-linux-ci/ba78bccb/check-final-acceptance.py --output /tmp/tr06-final-chain-replay.json
```

The strict actual-artifact replay is:

```sh
python3 docs/lean/proofs/TR-06/verification/check-linux-artifact.py \
  --ref ba78bccb76fe219b7686cab9bca61b845636ad7a \
  --artifact docs/lean/proofs/TR-06/verification/final-linux-ci/ba78bccb/artifact \
  --metadata docs/lean/proofs/TR-06/verification/final-linux-ci/ba78bccb/run-view.json \
  --job-log-gz docs/lean/proofs/TR-06/verification/final-linux-ci/ba78bccb/job-120742137176.log.gz \
  --archive docs/lean/proofs/TR-06/verification/final-linux-ci/ba78bccb/artifact-12543188710.zip \
  --artifact-metadata docs/lean/proofs/TR-06/verification/final-linux-ci/ba78bccb/artifact-12543188710.json \
  --output /tmp/tr06-final-replay.json \
  --reviewer 'Independent final retained-artifact replay'
```

These commands read retained actual CI evidence; they do not claim another local Linux execution. The canonical package remains permanently frozen at its 153 recorded hashes. Subsequent evidence and PR-description updates stay outside canonical inputs. No canonical input was edited by this verifier.
