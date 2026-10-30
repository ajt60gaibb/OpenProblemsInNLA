# Reproduce this independent final review

Use a Git repository containing source `669f3cd681b22882836d081a04652880ce39ba24`, its parent, candidate `0c6d3467`, full source `181c365d`, and executed merge `94c6ab3fe2773767905d0de0656d3d4e4bc019aa`. Fetching the merge object does not require a checkout or branch change. The approved v2 packet is retained in the separately sealed descriptive promotion review.

```sh
python3 review_postapplication.py \
  --repo /path/to/OpenProblemsInNLA \
  --packet /path/to/promotion-review/verification/v2/frozen-proposal \
  --output /path/to/new-postapplication-output
python3 collect_final.py --output /path/to/new-actual-ci-output
python3 audit_final.py \
  --repo /path/to/OpenProblemsInNLA \
  --evidence /path/to/new-actual-ci-output/collection/TERMINAL_TIMESTAMP \
  --output /path/to/new-actual-ci-output
```

The collector is read only against the GitHub API and requires authenticated `gh` plus network access. It asserts the exact final run/job/source head and writes original API, ZIP and job endpoint bytes. It collects the original executed/source commit metadata when terminal. The gzip is a derived deterministic lossless copy. The auditor safely reads the ZIP, reconstructs actual import closure and generated trust audit, verifies all package/provenance/original inputs, and binds every artifact log to the original raw job. It never runs Lean or Comparator locally.

The terminal collection is `actual-ci/collection/20261026T233713741782Z`. The accepted independent offline result is `actual-ci/audit-20261026T233840078839Z/RESULT.json`; earlier nonterminal snapshots are preserved with their original scope. The original candidate receipt remains separately sealed and is not substituted for the final run. `AUDITOR_PROVENANCE.json` records the reviewed independent template and explicit final-scope adaptations.
