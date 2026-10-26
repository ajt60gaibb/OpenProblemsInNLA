# TR-26 full-target author CI receipt

The corrected candidate passed all **2,391 author audit checks** against retained genuine Linux CI bytes. This is proof-author collection and mechanical audit; independent review and canonical promotion remain separate.

| Binding | Exact value |
| --- | --- |
| Candidate head | `fa85c05acc70bbaa05bb3346fb43b57b1546af67` |
| Reviewed full source | `ecc597cb68b65b473aecce9ac635e27d35c09694` |
| PR | [369](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/369) |
| Actual Lean run | [40396604016](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/40396604016) |
| Actual project job | [121831441827](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/40396604016/job/121831441827) |
| Executed checkout | `68b328659b93033184fd5d65316ef7abcaca9aab` |
| Checkout parent 1 | `ccc7864f5034cf7c4602f7577ceaf083ebf63d52` |
| Checkout parent 2 | `fa85c05acc70bbaa05bb3346fb43b57b1546af67` |
| Original artifact | `12688115670`, 44840 bytes |
| Original ZIP SHA256 | `f5f55dd18b6e3f92a6d504d4e5390f975bfe42ead6c3adbd2e72008dda2c279f` |
| Separate raw job log | `job-121831441827.log`, 128931 bytes |
| Raw job SHA256 | `b5d6d9a95d39cbd4177769742ed1f00e06ec2f58c4b0bee5eef8e61121b366b3` |
| Frozen author auditor SHA256 | `496b7f9093abbb2fa6583abd0e2ba386c792912335325dca405d29e5a3d2ebf6` |

The workflow and project job succeeded. The actual result reports `comparator-accepted` and `kernel-checked`. The audit binds all **857 Git inputs** (856 lock entries plus the lock itself), all 332 existing source-review bindings and the explicit omitted generated-bytecode record, all 84 runtime Lean sources, and the 80 byte-exact reviewed shared sources (77 proof modules plus three shared modules). It checks the raw checkout and exact Git parents, every retained artifact log body against the separately downloaded job log, actual tool and dependency pins, kernel/Comparator controls, theorem kinds and transitive axioms. It does not infer execution from current PR metadata.

The three actual Comparator theorem exports are:

- `NLA.Proofs.TR26.nonisotropic_degree`
- `NLA.Proofs.TR26.isotropic_degree`
- `NLA.Proofs.TR26.target`

Replaceable definitions are empty. Each theorem is checked with only `propext`, `Classical.choice`, and `Quot.sound`. Actual tools are official Lean 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, on `x86_64-unknown-linux-gnu`; Go 1.27.1 on Linux/amd64; Forsythe `8d1b0c0545a77b40245e84705aa7d273e6c81e62`. Full tool, executable and dependency hashes appear in the JSON receipt.

Raw inputs are retained in `retained/run-40396604016/terminal/`. The complete check report and extracted artifact are in `corrected-candidate-audit/`. Run the offline command in `README.md` to reproduce the mechanical audit using immutable Git objects. The author-only `SHA256SUMS` excludes the independent reviewers' evidence directories; `AUTHOR_MANIFEST_SCOPE.json` records that scope.

The earlier full candidate `f0fc0691c3496822e330894de60a9d6e94b7890a` remains explicitly rejected for package completeness, even though its workflow succeeded. Its original evidence and failed audit are preserved under `retained/run-40395797108/` and `diagnostics/f0fc-ignored-bytecode-input/`. No local author build is described as Linux CI. This receipt does not change problem IDs, originals, canonical Solved status, or verification metadata.
