# Required numbering CI — read-only code review

Reviewed 2026-09-11 in `/private/tmp/nla-review-wave2-20260911`. Published baseline `origin/main` was `aaa88c40fbf58e8cebc335021b3c5cd108c357e4` at both the start and end of inspection. No checkout, fetch, validator/test execution, workflow approval, remote mutation, or clone/shared-repository write was performed. This report alone was written outside the clone.

## Exact heads inspected

| PR | Head | Workflow and directly executed/imported local code versus published baseline |
|---|---|---|
| #68 | `2a1a0b39992bbd5654e7bdf9f869e21a6cee0d71` | Identical |
| #83 | `eadd702330dfdc56de30e429d4fb08340c66eafb` | Identical |
| #85 | `58a65609730306db4004352ccbdb5d8273ca2ff4` | Identical |
| #91 | `cc5ed78e4ca055f15717e5130f69bff6097d9406` | Identical |
| #93 | `c797aee814c8bebe4452329c93f5d84fd9c41f1f` | Identical |
| #103 | `6f5861fa392db467dc23abd096a02a08573146b8` | Identical |

The comparison covers the entire `.github/workflows/` and `tests/` trees, `tools/validate_problem_ids.py`, and its test-imported `tools/update_catalog.py`. All six also have an unchanged `problem_ids.json`. File-tree inspection found no added root Python module/package or added test/tool module that would shadow the inspected imports. The direct execution chain was read in full. Submission scripts under `references/` and rendering scripts are not imported or executed by this workflow; this review does not approve executing those scripts.

## What the required check does

Workflow: **Permanent problem IDs**. Single job: **Validate permanent problem IDs**, on `ubuntu-latest`. Triggers are `pull_request` and `push`; there is no `pull_request_target` trigger, elevated job, reusable workflow, deployment, package installation, or artifact-upload step.

- Declares only `permissions: contents: read`. It does not request write permissions, a PAT, repository secrets, or OIDC permission.
- Runs `actions/checkout@v4` with `fetch-depth: 0` and `persist-credentials: false`. No repository or ref override is supplied. For the PR event it therefore checks out the normal event merge result, not an explicit `pull_request.head.sha` override. A later changed merge result remains subject to the actual required CI result. The documented checkout behavior includes network retrieval from GitHub and writing/cleaning the ephemeral runner workspace; it does not persist its authentication in checkout Git config. The action remains an existing **major-version tag**, not an immutable action-commit pin. See the [official v4 README](https://github.com/actions/checkout/blob/v4/README.md).
- Invokes the validator against `refs/remotes/origin/$DEFAULT_BRANCH`, then against the event’s base SHA / previous push SHA when nonempty and nonzero. Values enter via environment variables and quoted shell arguments, rather than interpolation into shell source. The validator resolves the supplied ref using `git rev-parse --verify --end-of-options`, then reads the resolved Git tree.
- Runs `python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v`.

## Local code behavior and side effects

The validator uses only Python’s standard library and local Git. It reads canonical README headings and the registry, checks ID/path agreement and symlinks, and compares published IDs and per-prefix maxima. Its subprocess calls are argument-list invocations of read-only `git rev-parse`, `git ls-tree`, and `git show`; there is no shell execution, download, dependency installation, or network client.

The 17 unit tests import the unchanged validator and indexer. They create and delete synthetic files, symlinks, and Git histories **inside `tempfile.TemporaryDirectory()`**, including local `git init/add/commit/update-ref`. No remotes are configured or contacted. The sole indexer invocation patches its `ROOT` to that temporary directory and intentionally fails validation before writing indexes; the test checks that the fixture files remain unchanged. The indexer’s generation routine is otherwise not called. Ordinary Python import caches may be written in the ephemeral checkout. No workflow step commits, pushes, merges, changes repository settings, or writes the real catalogue.

## Conclusion and authorization boundary

No new executable behavior, weakened numbering safeguard, permission escalation, custom dependency installation, or submission-code execution was found in these six required workflows relative to the published baseline. The expected external access is the existing GitHub checkout/action infrastructure; the validator/tests themselves require no network.

This is evidence describing the six specific required checks, **not authorization to approve or run them**. The coordinating task reports that automatic approval review previously required explicit user permission for approving the fork workflow runs beyond the request to merge. That permission remains required; this read-only review neither bypasses nor replaces it. CI pass/fail results and actual mergeability were not assessed here.
