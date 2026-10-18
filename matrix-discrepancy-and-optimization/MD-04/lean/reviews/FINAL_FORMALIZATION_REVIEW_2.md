# MD-04 final formalization review 2

**Phase:** final proof and promotion source review, 16 October 2026.

**Reviewer:** Codex agent `/root/md03_second_referee` (AI), acting as a second independent MD-04 referee. I did not implement this proof and did not use the first referee's report as evidence. This is not a human endorsement.

**Verdict:** **APPROVE** the exact MD-04 formalization identified below. This approval is specific to the listed source bytes and pinned imported theorem boundary; the catalog promotion also requires the separate mechanical gates and both retained project review reports.

## Reviewed source identity

I read the clean main checkout at `47006df8b3a6c724a557266c891893d03e69323a` and the proposed standalone MD-04 checkout at `358c6de4d68664ed145e77680bbdd75a2e4ce6c2`. These 15 project files are byte-identical between those checkouts; SHA-256 values are from the proposed checkout:

| Project-relative file | SHA-256 |
| --- | --- |
| `ORIGINAL.md` | `a8be36a5217cb0b3031c8f87cfc25e5421ca78dd8c42ecc151219fa62eb8156e` |
| `NUMERICAL_TARGETS.md` | `04c60b361770523bcca06ddc80f9b5334464339432497a76e3250e31e677f757` |
| `NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `NLA/Statements/MD03.lean` | `2638d903c1ccc478da9941f76d1903d838e4f6c5434ec1792dc1fbf811446b05` |
| `NLA/Statements/MD04.lean` | `c3536d295078f8223c82046f80f2d4a02eee5310cd07125013d303991ae41894` |
| `Reviewed/MD03.lean` | `b86ff4b7f6268713024a85e81dd87793a04e288925b683a91febeee842426516` |
| `Reviewed/MD04.lean` | `e7893db1c2656e6834009267738b6244c1b0e60dde582a525b0009ae079c7257` |
| `NLA/MD03/Proof.lean` | `3e38a245007e2b860adacd97b89046d49b90f0f8e681dd5db43cafef6e97e93c` |
| `NLA/MD04/Reduction.lean` | `d05b5b76206215f4c63d400f85a2dd70a40718a71fcb406c033937b7f88525e2` |
| `NLA/MD04/Proof.lean` | `e6510ed6ee38cc9407b5babae4e13db85dce9139f0abb4478ec44ce7a3b2ce91` |
| `Challenge.lean` | `b62b97989a48f9d3936cad7a41b20a899d99692b449d7d421bc1413603f39260` |
| `Solution.lean` | `9cd9c0c8ae1d0789800951e731b44ef75aca007a34484f4047e991c00d121531` |
| `Identity.lean` | `9ffdbed7fa28f8fba7a4facb70ed4fec8003ab9bc82c102db65f977288cc970a` |
| `comparator.json` | `a456d61c696bc42a45d1f388290b8d9ed50d0a97406b98bfe953e4af83583f70` |
| `lake-manifest.json` | `b08be09c6c5cbe2f906796293c7de2d95b4601495b77c4073e9b70c6fa364034` |

The project MD-03/MD-04 statement and frozen copies match their `lean-statements/` counterparts by hash. `Identity.lean` checks both live/frozen target equalities by `rfl`. The copied MD-03 bridge matches the separate MD-03 project at SHA-256 `3e38a245007e2b860adacd97b89046d49b90f0f8e681dd5db43cafef6e97e93c`. The canonical original remains `matrix-discrepancy-and-optimization/MD-04/README.md`; its permanent ID and mathematical question are unchanged.

## Fidelity, scope, and proof path

`NLA.Statements.MD04.Target` places one positive real constant `C` before all natural `m,n,t` with `0<m`, `0<n`, and inclusive `1≤t≤m`. For every real `Fin m × Fin n` matrix with each entry exactly `0` or `1` and every column sum at most the real cast of `t`, it asks for one real sign per column (`-1 ∨ 1`) and a weak absolute signed row-sum bound `C * Real.sqrt (t : ℝ)` for every row. This matches the original infinity-norm target; the statement adds no matrix subclass, online constraint, constructive demand, or hidden conclusion. The `t=1` and `t=m` endpoints are included. The `t=0` case is excluded just as in the canonical problem.

In `NLA.MD04.of_komlos`, the `1≤t` premise gives `(0:ℝ)<t`, so `Real.sqrt t>0`. For `B i j = A i j / Real.sqrt t`, each `0/1` entry satisfies `(A i j)^2=A i j`, while `(Real.sqrt t)^2=t`. Thus the full squared column sum for `B` equals `(∑ i, A i j)/t≤1` using the stated column premise. The proof passes the same positive `m,n` and this `B` to the reviewed `NLA.Statements.MD03.Target`. It receives signs for every column and a bound for every row, then proves the signed row sum of `A` equals that of `B` times `Real.sqrt t`; positivity permits scaling the absolute bound to `C * Real.sqrt t`. There is no dropped endpoint or extra premise. The reduction does not need `t≤m`, so its argument covers a stronger sparsity range while its conclusion retains the original `t≤m` quantifier.

`NLA.MD04.target` applies this reduction to `NLA.MD03.target`, whose copied bridge uses the pinned Gabriel Dahia Komlós theorem to supply **exactly `C=36`**. I inspected the imported source at [`gdahia/Komlos` commit `fac7d8f71f08caac7f5fe67786abe387cfe18b10`](https://github.com/gdahia/Komlos/tree/fac7d8f71f08caac7f5fe67786abe387cfe18b10), specifically `Komlos/Main.lean` and `Komlos/Discrepancy.lean`: `Komlos.discrepancy_le_of_forall_sum_sq_le_one` gives `discrepancy A≤36` from exactly the squared column premise, and `discrepancy_le_iff` plus `colouringDiscrepancy_le_iff` yields explicit `±1` signs and all row bounds. The local bridge reverses only the order of the sign disjunction. The MD-04 scaling preserves this same `36`, which suffices for the original existential target. It does not formalize the sharper `3√(2π)` historical Guo–Fang–Lu constant.

`Challenge.lean` has the single deliberate specification `sorry`. `Solution.lean` imports `NLA.MD04.Proof` and does not import `Challenge`. `comparator.json` selects `NLA.MD04.target`, has no replaceable definitions, and permits only `propext`, `Classical.choice`, and `Quot.sound`. No local solution source contains `sorry` or a newly declared axiom. The substantive imported proof is Dahia's formalization following Karingula and Lovett; Arav Bhattacharyya and OpenAI Codex are credited for the local bridge and reduction. The separate Guo–Fang–Lu resolution and George Stepaniants application note retain their historical attribution.

## Mechanical evidence inspected and limits

I inspected the [13 October 2026 MD-04 GitHub job log](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/38392383534/job/115299684643). It built the separate Challenge and Solution, reported `NLA.MD04.target` transitive axioms `[propext, Classical.choice, Quot.sound]`, then printed `Lean default kernel accepts the solution`, `Your solution is okay!`, and `PASS: fresh Comparator run and all controls`. GitHub lists artifact `lean-MD-04`, ID `11819721631`, with ZIP digest `de0afa8b12b7eac789aa0162f7fb1613df7dff99a6a76ca45eee3154f2b1a97b`. The job checked PR #354's merge checkout `4b5be52826d24d0e640862cf1a5a5620cc8d0312`. I fetched that checkout's MD-03 bridge, MD-04 reduction and final proof, MD-04 target, Challenge, Solution, and comparator configuration through GitHub; their decoded UTF-8 content equals the proposed checkout's corresponding files. The proof modules set `leancert.trust "kernel"` and assert kernel trust, as the retained [CI receipt](../../../../docs/lean/proofs/MD-04/LINUX_CI_RECEIPT.md) describes.

I did not perform a fresh Lean build or Comparator run, inspect the artifact archive's `result.json` myself, or independently reprove the external Komlós library. The CI job establishes kernel checking of pinned proof terms; it does not semantically review every external lemma. This source review covers the complete local target, scaling reduction, final application, Challenge boundary, and the exact imported declarations used. A change to any listed source hash or the Komlós revision reopens this approval.
