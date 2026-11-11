# RE-06 pre-proof review packet

Author-only packet for the exact published RE-06 target at `099805ef1ce7347d373e47cccc3b2d7cf580a99e`; no mathematical implementation or approval.

Read `CONTRACT.md`, `Challenge.lean` and `READINESS.md` against `INPUT_LOCK.json` and its byte-preserved `originals/`. `REUSE_LOCK.json` binds supplementary existing TR-04 exact-SVD source and its original review provenance; it does not approve RE-06. `PACKET_LOCK.json` freezes this packet's files before the new independent reviews.

Replay from the repository root, choosing a fresh output directory:

```sh
python3 reviews/2026-10-23-solved-lean/re06-next/audit_inputs.py --output /private/tmp/re06-input-replay.json
python3 reviews/2026-10-23-solved-lean/re06-next/reproduce_scaffold.py --output /private/tmp/re06-scaffold-replay
```

Both scripts accept explicit path options; `--help` lists them. Scaffold replay uses a fresh project object directory and the exact pinned runtime/dependencies, and checks actual kernel rejection of all six theorem holes. Its negative cases must fail Lean. The retained 14/14 author result demonstrates statement compatibility and trust enforcement, not an RE-06 proof. No canonical file, ID, original target, shared model or package pin is modified.

Required next action: two independent non-author reviewers inspect the same frozen contract/input/signature hashes and explicitly approve before proof implementation. Author evidence and prior statement/SVD reviews cannot substitute for those approvals.
