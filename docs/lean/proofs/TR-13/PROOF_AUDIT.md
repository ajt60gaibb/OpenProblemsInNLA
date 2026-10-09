# TR-13 independent local proof and trust audit

**Reviewer:** `/root/proof_inventory` (AI agent), 9 October 2026.
**Verdict:** PASS for a fresh local Lean build, LeanCert kernel trust audit,
and a source scan of the live proof import tree. The existing full-target
theorem was not edited. This is not a mathematical line-by-line review of every
proof argument or the repository's isolated Linux Comparator result.

## Reproduction and result

Working directory: `tensor-computations/TR-13/lean`. Toolchain: Lean 4.33.1
arm64 macOS, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
Mathlib checkout: `0df444a360eaa60ab8c11dca51a86af692955474`.
LeanCert checkout: `621a43d7cf21f87872392a01e874f2f1dbddc926`.
The ignored `.lake/packages` entries point at those pinned local checkouts.

```sh
PATH=/Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean/.tools/lean-4.33.1-darwin_aarch64/bin:$PATH lake build Solution
```

Exit code 0: `Build completed successfully (3411 jobs)`. The 13 project
`NLA.TR13` modules and `Solution` were built freshly in this project; pinned
dependency build artifacts were reused.

In a separate temporary source file, I imported `Solution` and
`LeanCert.Tactic.Verification`, set `leancert.trust` to `"kernel"`, and ran
`#print axioms` plus `#assert_trust kernel` on four declarations. The complete
audit source was:

```lean
import Solution
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

#check NLA.TR13.generic_rank_equality
#print axioms NLA.TR13.generic_rank_equality
#assert_trust kernel NLA.TR13.generic_rank_equality
#print axioms NLA.TR13.generic_vandermonde_upper
#assert_trust kernel NLA.TR13.generic_vandermonde_upper
#print axioms NLA.TR13.generic_border_lower
#assert_trust kernel NLA.TR13.generic_border_lower
#print axioms NLA.TR13.all_ranks_equal_of_bounds
#assert_trust kernel NLA.TR13.all_ranks_equal_of_bounds
```

`lake env lean /private/tmp/TR13ProofTrust.lean` exited 0. Each declaration's
transitive axiom report was exactly `[propext, Classical.choice, Quot.sound]`.
LeanCert's `#assert_trust kernel` rejects `sorryAx`, native compiler trust and
unrecognized custom axioms; all four checks passed. The temporary audit source
has SHA-256
`f1bd5907fee126593e80eb6c808d83ab3650a4de184981bee18bae54389be9b9`.
Its commands are reproduced above so the check does not depend on retaining a
file outside the repository.

## Source trust scan

I inspected the imports and scanned `Solution.lean` and every one of its 13
project-local `NLA/TR13/*.lean` dependencies for `axiom`, `sorry`, `admit`,
`unsafe`, `opaque`, `constant`, `native_decide`, `run_tac`, `implemented_by`,
`set_option`, and `#eval`. No proof escape or unproved declaration was found.
`Solution.lean` imports `Upper`, `Lower`, and `RankComparison`, and none of
their local imports is `Challenge.lean`. The separate `Challenge.lean` has an
intentional `sorry` and was not a dependency of the successful audit.

This source scan supplements the transitive axiom audit; it does not establish
that every mathematical lemma has been independently read and checked against
the informal manuscript. The [statement review](statement-review-proof_inventory.md)
checks the exported theorem's scope separately. No `Lean verified` status
change follows from this local result alone.

## SHA-256 of pinned and live inputs

| Repository-relative path | SHA-256 |
| --- | --- |
| `tensor-computations/TR-13/lean/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `tensor-computations/TR-13/lean/lakefile.toml` | `aded4a942bb9a98929e564c1ac8464a7f8f43c08e4e0d6d2833a9b91f60b6ff5` |
| `tensor-computations/TR-13/lean/lake-manifest.json` | `431a2cba1225a9ab974b43b11a366f735f4c5b6621039b72c2044a8451bda293` |
| `tensor-computations/TR-13/lean/Solution.lean` | `cca409d68bd917f58e8d97eaeded957ea4f4e3337b68a315b5d23b1cba32905e` |
| `tensor-computations/TR-13/lean/NLA/TR13/Compression.lean` | `a3c3ae15b0a4c0c1585bd2314a994a54f2b27e0cbc0cdf32447470647025702b` |
| `tensor-computations/TR-13/lean/NLA/TR13/Definitions.lean` | `f026f45877d8e2bfc94a96c8be0dece8a1f2a843d8c1b7249891d720c42240c7` |
| `tensor-computations/TR-13/lean/NLA/TR13/Koszul.lean` | `4b5d51a9c32de19ba90507522e41567f7e1452c8983e435481b96310ddba87eb` |
| `tensor-computations/TR-13/lean/NLA/TR13/KoszulWitness.lean` | `027d7f54fec3fbc88c1b5c0eb7ccd7932caf2c06d37044cb26f404063423b315` |
| `tensor-computations/TR-13/lean/NLA/TR13/Lower.lean` | `55a8d56cb1c5afed1894da71e92eb77a0fc002825fe97d32563489e285733b76` |
| `tensor-computations/TR-13/lean/NLA/TR13/LowerRank.lean` | `bf7afd3d2b04ea9daf42aa54260f1ba8f0f1e7da49e091d0c4b4e07582410602` |
| `tensor-computations/TR-13/lean/NLA/TR13/MatrixCertificate.lean` | `a94e4eb3185101220c8a8192bb3beb2a3ff8fcfadf35f9267f47fc83ccb6b491` |
| `tensor-computations/TR-13/lean/NLA/TR13/Prony.lean` | `c80589f9124cbfb5adf3fb50f93fefa6a14303e0e4f5849d67efe0e5c14ca810` |
| `tensor-computations/TR-13/lean/NLA/TR13/PronyPolynomial.lean` | `cb800a6c18d7a23af8b54d1de9b6997909456bc85483bfbbe600173cab287ac8` |
| `tensor-computations/TR-13/lean/NLA/TR13/PronyWitness.lean` | `47629f85085fce41da5856ca5f6e7f1844abec4f8a35e93fe0aa87bb3763f337` |
| `tensor-computations/TR-13/lean/NLA/TR13/RankComparison.lean` | `555d6e6ee61f29a4ddc3c199a1ee9ab71ea6a132961f92d2ce352a9817fdd6e3` |
| `tensor-computations/TR-13/lean/NLA/TR13/Upper.lean` | `f02165febe8d37e531ba767e2bfdc3bd8467c68a39556e4e55b67bcb8867e8d9` |
| `tensor-computations/TR-13/lean/NLA/TR13/UpperPolynomial.lean` | `cc7d7d7928a6becf3410f5148f94bad8dc91b0684d887c945e38e944c4eaa7a1` |
