# MD-03 final formalization review 2

**Phase:** final proof and promotion source review, 16 October 2026.<br>
**Reviewer:** Codex agent `/root/md03_second_referee` (AI), independent of the implementation and of the first referee. This is not a human endorsement.<br>
**Verdict:** **APPROVE** the exact MD-03 formalization identified below. The approval is specific to these source bytes and the stated imported theorem boundary. The catalog promotion also requires the separate mechanical gates and the project's two retained review reports.

## Reviewed source identity

I read the clean main checkout at `47006df8b3a6c724a557266c891893d03e69323a` and the proposed standalone PR #358 checkout at `cb6679cacabe72ab50be052404b6a50d96059050`. The proof, statements, and wrappers listed here have identical SHA-256 hashes in both checkouts:

| Project-relative file | SHA-256 |
| --- | --- |
| `ORIGINAL.md` | `3486bfa69ba99b106dfb059866d0f4fa3e0b9eac99276a05f911756639bbfd1e` |
| `NUMERICAL_TARGETS.md` | `2c4d379de6e7b639ef90df30c19319b9f7a36951de085d9bd3180931885063c0` |
| `NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `NLA/Statements/MD03.lean` | `2638d903c1ccc478da9941f76d1903d838e4f6c5434ec1792dc1fbf811446b05` |
| `Reviewed/MD03.lean` | `b86ff4b7f6268713024a85e81dd87793a04e288925b683a91febeee842426516` |
| `NLA/MD03/Proof.lean` | `3e38a245007e2b860adacd97b89046d49b90f0f8e681dd5db43cafef6e97e93c` |
| `Challenge.lean` | `ca4666f80ec116398c2e2181821b0d18a161ea6fa1010cfdd19d179eb9cea6d7` |
| `Solution.lean` | `a32f921a30d4b743f92356f80039a92e1a1076f7cff72bb3e8af388cf6aba672` |
| `Identity.lean` | `a7189d284bee92451b7c1747cd88a28880749e1298ec019f5e0b891ec7dfb757` |
| `comparator.json` | `5d1dd3060edf739ff83a841fed4b94ad0c0c9778f0c24eaf4f8e0ad8e64b4383` |
| `lake-manifest.json` | `f6b9b89663de18119cff0e92f4fdcf46c335acf59ef01eedb351dad0bf4c7428` |

The project statement copies match their shared `lean-statements/` counterparts by hash. `Identity.lean` checks `NLA.Statements.MD03.Target = NLA.ReviewedStatements.MD03.Target` by `rfl`. The original canonical question remains `matrix-discrepancy-and-optimization/MD-03/README.md`; this PR does not change its permanent ID or mathematical target.

## Fidelity and proof path

`NLA.Statements.MD03.Target` asks for one positive real `C` before all positive natural dimensions `m,n` and all real `Fin m × Fin n` matrices. Its sole matrix premise is the full squared column sum `∑ i, (A i j)^2 ≤ 1` for every column. It asks for a real sign at every column and the weak absolute signed row-sum bound for every row. These are the original quantifiers, norm, endpoints, and real domain. There is no hidden regularity condition, matrix subclass, algorithmic requirement, or conclusion packed into a custom predicate.

I inspected the pinned external source at [`gdahia/Komlos` commit `fac7d8f71f08caac7f5fe67786abe387cfe18b10`](https://github.com/gdahia/Komlos/tree/fac7d8f71f08caac7f5fe67786abe387cfe18b10), specifically `Komlos/Main.lean` and `Komlos/Discrepancy.lean`. `Komlos.discrepancy_le_of_forall_sum_sq_le_one` accepts an arbitrary finite real matrix with exactly the column-square premise and concludes `discrepancy A ≤ 36`. `Komlos.discrepancy_le_iff` converts that bound to an attained colouring; `Komlos.IsColouring` means each value is `1 ∨ -1`. `Komlos.colouringDiscrepancy_le_iff`, with `0 ≤ 36`, converts its norm bound to `∀ i, |∑ j, A i j * χ j| ≤ 36`. Thus `NLA.MD03.signing` only reverses the disjunction to the reviewed `-1 ∨ 1` order. `NLA.MD03.target` supplies `C = 36`, proves `0 < 36`, and introduces all reviewed quantifiers. The imported theorem is actually used; the proof does not assume the target or substitute a weaker statement. It even proves `signing` without requiring positive dimensions, while the target uses only positive ones.

The constant `36` is exact in the imported conclusion, bridge, and target witness. It is larger than the historical Guo–Fang–Lu bound `3√(2π)`, but the canonical problem asks for existence of some universal positive constant. No numerical certificate or approximate inequality is involved in this bridge.

`Challenge.lean` has one deliberate `sorry` in the isolated specification fixture. `Solution.lean` imports `NLA.MD03.Proof` and the live and frozen statements; it does not import `Challenge`. `comparator.json` selects only `NLA.MD03.target`, has no replaceable definitions, and permits `propext`, `Classical.choice`, and `Quot.sound`. The imported Komlós proof remains a substantial external formalization by Gabriel Dahia, following Karingula and Lovett; the local project is a thin translation. The historical Guo–Fang–Lu resolution and George Stepaniants application-note credits remain distinct from this Lean proof.

## Mechanical evidence inspected and limits

I inspected the [13 October 2026 GitHub job log](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/38392383534/job/115299684562) for the `MD-03` project. The final target line reports `NLA.MD03.target` with transitive axioms `[propext, Classical.choice, Quot.sound]`; the final Comparator run says `Lean default kernel accepts the solution` and `Your solution is okay!`. GitHub lists the uploaded `lean-MD-03` artifact as ID `11820571299`. The job checked PR #354's merge checkout `4b5be52826d24d0e640862cf1a5a5620cc8d0312`. I fetched that checkout's `NLA/MD03/Proof.lean` through GitHub and compared its decoded UTF-8 content with the PR #358 file; the content is identical. The project source sets `leancert.trust "kernel"` and `#assert_trust kernel target`; the retained CI receipt records the associated checker result and dependency pins.

I did not run a fresh Lean build or Comparator job, inspect the downloaded artifact archive's `result.json`, or independently reprove the imported Komlós theorem. The CI job is evidence of checking the pinned proof terms, not a semantic audit of every lemma in the external library. This review independently audits the complete local statement, its bridge, and the imported declarations it calls. A later change to any listed input hash or to the Komlós pin requires a new review.
