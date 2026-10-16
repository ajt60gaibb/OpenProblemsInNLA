# MD-04 isolated Linux proof receipt

The [Lean verification run](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/38392383534) for merged PR [#354](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/354) completed successfully on 13 October 2026. Its [MD-04 job `115299684643`](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/38392383534/job/115299684643) ran on Ubuntu 24.04 against PR merge commit `4b5be52826d24d0e640862cf1a5a5620cc8d0312` (head `a173f75d5d79d9d6932c17790fe1f02a0a75e28f`). It selected only the MD-04 project in this matrix job. Manifest validation, unprivileged Linux isolation, strict-sandbox regression controls, the fresh Comparator run, and log upload all passed.

The job built the separate Challenge (1,566 jobs) and Solution (8,732 jobs). Comparator exported `NLA.MD04.target` from both, ran Lean's default kernel on the solution, printed `Lean default kernel accepts the solution` and `Your solution is okay!`, then the verifier printed `PASS: fresh Comparator run and all controls`. The target's transitive axiom report was exactly `[propext, Classical.choice, Quot.sound]`; the only `sorry` was the intentional Challenge hole. The actual proof modules set `leancert.trust "kernel"` and assert kernel trust. The generated artifact's `result.json` records `result = comparator-accepted` and correctly says `semantic_review = not-performed-by-this-command`; the separate [independent review](INDEPENDENT_REVIEW.md) supplies the semantic check.

The uploaded artifact [`lean-MD-04`](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/38392383534/artifacts/11819721631) has ID `11819721631` and ZIP SHA-256 `de0afa8b12b7eac789aa0162f7fb1613df7dff99a6a76ca45eee3154f2b1a97b`. I downloaded and inspected its `result.json`, `comparator.log`, kernel controls and sandbox controls. All 31 `input_sha256` entries in that receipt matched the corresponding project files on `origin/main` before this evidence-only update. The proof, challenge, target, comparator configuration, toolchain and dependency pins are unchanged by this PR.

| File in artifact directory `verify-20261013T134718Z-3982/` | SHA-256 |
| --- | --- |
| `result.json` | `8dfddc9723e1581890634656d8d0f4c086740bfb784e41d1d91aaca636253dcf` |
| `comparator.log` | `949cef9c7d44bdacfeddf02f09159954bb11cc5f70a8866dc7c9e4e97985f830` |
| `kernel-controls.log` | `ac5884a6a9aab533b23369a1a9a4e453f745264bbaeb2e13d60d94569c45a361` |
| `sandbox.log` | `388774aad07fecb28749f10d2a7f363509d158b1432fd742b21f9258dfb69e75` |

The receipt records Lean `4.33.1` on `x86_64-unknown-linux-gnu`, `source_lock_sha256 = b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`, and these proof inputs:

| Project file | SHA-256 |
| --- | --- |
| `NLA/Statements/MD04.lean` | `c3536d295078f8223c82046f80f2d4a02eee5310cd07125013d303991ae41894` |
| `NLA/MD03/Proof.lean` | `3e38a245007e2b860adacd97b89046d49b90f0f8e681dd5db43cafef6e97e93c` |
| `NLA/MD04/Reduction.lean` | `d05b5b76206215f4c63d400f85a2dd70a40718a71fcb406c033937b7f88525e2` |
| `NLA/MD04/Proof.lean` | `e6510ed6ee38cc9407b5babae4e13db85dce9139f0abb4478ec44ce7a3b2ce91` |
| `Challenge.lean` | `b62b97989a48f9d3936cad7a41b20a899d99692b449d7d421bc1413603f39260` |
| `Solution.lean` | `9cd9c0c8ae1d0789800951e731b44ef75aca007a34484f4047e991c00d121531` |
| `comparator.json` | `a456d61c696bc42a45d1f388290b8d9ed50d0a97406b98bfe953e4af83583f70` |

The earlier macOS attempt in the MD-04 project remains a historical local record; this later Linux job supplies the authoritative isolated result. A fresh run of the repository's verifier is reproducible with `bash tools/lean/bootstrap.sh /tmp/nla-md04-checker` followed by `bash tools/lean/verify.sh matrix-discrepancy-and-optimization/MD-04/lean /tmp/nla-md04-checker` on a supported non-root Linux host.
