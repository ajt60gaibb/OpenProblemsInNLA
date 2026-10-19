# TR-14 actual PR Linux run — source correspondence, strict receipt pending

Reviewer: `/root/lean_verification`, independent Codex AI agent, 18 October 2026.

The actual PR workflow [39168848423](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39168848423), job [117797923198](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39168848423/job/117797923198), completed successfully. Its retained original artifact is `12151594666`; the ZIP SHA-256 is `da46d76543b0c569604391e86a3a79a369d2bc5e9c778cf74f4475130d120010`, matching GitHub artifact metadata and the raw job upload digest.

The unchanged committed checker was independently replayed with this reviewer's explicit attribution against proof head `54dcced753d75e70a6592bd50b1e3daa7af2ca7e`. **The strict replay correctly fails: 40 of 41 checks pass, and `harness-source-commit` fails.** The workflow event is `pull_request`, its head is `54dcced...`, and its actual checked-out/harness-recorded repository commit is GitHub's synthetic merge `d5c9b7677f8683fc687e9daca18493f4dd2075cb`. No check was removed or relaxed, and this report does not approve promotion or call this a strict proof-head receipt.

The actual logs nevertheless contain successful default-kernel, Comparator and LeanCert kernel checks of the complete selected `NLA.TR14.target`, with only `[propext, Classical.choice, Quot.sound]`; actual sandbox, kernel/Comparator regression and negative sorry/native controls also pass. The source correspondence checks, exact 82-Lean-input set, all 139 recorded input hashes against the proof head and current package, exact project file sets, generated trust consumer, pinned real Linux tools, original ZIP digest and exact extraction checks all pass. The failed machine-readable replay remains retained as `independent-pr-proof-head-attempt.json`.

To identify the actual merge source without changing that verdict, I independently read and retained GitHub's commit and Git-tree metadata. The merge parents are `ed4262cd30d832ea4b0c657371247a7e0f748818` and the exact proof head `54dcced...`. Complete subtree path chains from the merge root verify:

- All **139 canonical project files**, including all **82 actual Lean inputs**, have exactly the same Git blob object IDs and bytes as the proof head. Their SHA-256 map equals the actual harness `input_sha256` map.
- All **18 files under `tools/lean`** are identical to the proof head, including the actual harness and source lock.
- All **four workflow files** are identical to the proof head.

The merge root tree is `853721b77f685848a52e195e5f6e2e766ac0a51a`; the actual complete project subtree is `f55aa41a9ba6bf48b429436fcaece97f100d2751`. GitHub truncated an initial repository-wide recursive tree response. That response is preserved but is **not** used as complete evidence: the independent correspondence check uses individually complete small subtrees and verifies every path chain from the actual merge root instead.

```bash
python3 docs/lean/proofs/TR-14/verification/check-pr-merge-correspondence.py \
  --ref 54dcced753d75e70a6592bd50b1e3daa7af2ca7e \
  --evidence docs/lean/proofs/TR-14/verification/full-linux-ci
```

The separate machine-readable correspondence result records `source_correspondence_passed: true`, **`strict_proof_head_receipt_passed: false`**, and **`promotion_approved: false`**. All original logs/ZIP/metadata, strict failed replay, retained GitHub metadata, source correspondence driver and results are outside the canonical project in [verification/full-linux-ci/](verification/full-linux-ci/). The exact push-run artifact remains the requested strict receipt gate. This review independently inspects actual retained evidence; it does not claim to rerun Linux locally or provide external human endorsement.
