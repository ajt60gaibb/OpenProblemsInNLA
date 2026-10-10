# MF-03 orders 1–15: independent final proof review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026. **Verdict:** APPROVE frozen `FiniteRange.lean` as a kernel-checked proof of the exact MF-03 target clause for every integer order `1≤m≤15`, including existence of a reduced normalized pair and the universal closed-disk bound for **every** reduced normalized pair. Its explicit `m≤15` hypothesis means it is not the all-order MF-03 `Target`.

The public `target_through_fifteen` signature reproduces the frozen Target's positive-order conclusion verbatim after the additional upper-order hypothesis: `∃ P Q, ReducedPadeRepresentation m P Q`, and for all reduced `P,Q` and all complex `z` with `‖z‖≤3`, `Q.eval z≠0` and `‖1−P.eval z/Q.eval z‖≤2`. The disk boundary, weak constant two, normalization, coprimeness, and universal tested-pair quantifier are all retained. An independent imported `#check` confirmed this elaborated type.

The private helper applies the reviewed generic `normalized_exists_reduced` to a **supplied** normalized pair for the existential conjunct. It then applies `disk_bound_for_every_reduced_pair` to the supplied pair's full disk certificate and any tested reduced pair. This correctly upgrades a possibly non-coprime rational certificate to the complete same-order target clause; it does not assume the source pair was already reduced. The cross-product identity from Reduction is used in its own proof, and the transport lemma supplies the universal conclusion.

The finite dispatch has exactly 15 branches after `1≤m≤15`: order `1` uses `order_one_target_clause`; orders `2,…,15` each apply the corresponding `order_two_*` or `finiteXX_*` normalized and disk theorems to the helper. There is no gap at either endpoint, no branch for order zero, and no inference for order sixteen or above. The private certificate polynomial arguments are inferred from each public theorem's type, so private witness names do not hide an assumption. The order-specific rational coefficients, complete equations through `2m`, and exact disk budgets were independently reviewed separately.

I ran a separate pinned Lean 4.33.1 import audit with `#assert_trust kernel` and `#print axioms` on `target_through_fifteen`. It passed and printed only `[propext, Classical.choice, Quot.sound]`; the author's pinned module build and direct source compilation also passed. A source scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

## SHA-256 of frozen closure

| Input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/MF03/FiniteRange.lean`** | **`b83eadb2aa7bb33dfaf8f553be0ae16df5cab60762a90ff11cea2e609f38278a`** |
| Frozen `NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `NLA/Proofs/MF03/Reduction.lean` | `0e58cdba5a4302aa025201e73143a4c3056f33fc43c618da6bf4aa0095da89cb` |
| `NLA/Proofs/MF03/Transport.lean` | `902e6c7caf52f462d2bc11fcdf713306f69d67d8da0a159b01713ae31fc6cb66` |
| `NLA/Proofs/MF03/OrderOne.lean` | `924c8437e430808f183ff104ee01ba9a1771ccf892a4bb9c37e26ad7c902ca48` |
| `NLA/Proofs/MF03/Finite02.lean` | `d1127741afc7ec96469d2a9d6e6c4f6be08d3e1e49cf7bb807760ffc2119097e` |
| `NLA/Proofs/MF03/Finite03.lean` | `45ad66cf9ea996dd5ce1a8de884659fac739215c9db2f701ff9ae7e9a66af30b` |
| `NLA/Proofs/MF03/Finite04.lean` | `97baa4b71888cb97a6116e26a1d5f1a7d631611b0969a68e80b7f325a5287ee7` |
| `NLA/Proofs/MF03/Finite05.lean` | `bc6d2219c84438846b9b6c081b2d9332931c15e9047781560b713a1611545181` |
| `NLA/Proofs/MF03/Finite06.lean` | `d8acae03b23c3bebd8309ae9da25b2ac261ba52e5fea41cbfa56ad12b6313a4c` |
| `NLA/Proofs/MF03/Finite07.lean` | `5938ae3bf906a1835b0cce737ce5a427465a1255ebd43c757c821248b57a8e21` |
| `NLA/Proofs/MF03/Finite08.lean` | `ee431488e3d090efdc4db47fdbe76ee96fdf388a92445f1fda719da78a8e2979` |
| `NLA/Proofs/MF03/Finite09.lean` | `5beb2f01343aa7aa5bdf22242498181aa72889b6b92a1fb99f44a42cb9d5c871` |
| `NLA/Proofs/MF03/Finite10.lean` | `54742c4fddd08254768482620523e9e141ba49fabaf9344ee7247d66b127c835` |
| `NLA/Proofs/MF03/Finite11.lean` | `83f555893cc34ff6a8e5701e1a722b751aa0b3eeab362e2736d0f45b8484a6c4` |
| `NLA/Proofs/MF03/Finite12.lean` | `3304258460f2bb9fbebb792cb42642c72566fd706facfae56bef5a5d5051fa2b` |
| `NLA/Proofs/MF03/Finite13.lean` | `6b2ab289fcf4ed57f72fb3707513338fa984bb6ac920d4968a7dc660b7dacd91` |
| `NLA/Proofs/MF03/Finite14.lean` | `b28d1ec6b0422559133253607384e195dc388c5d829625a86dfd83d28e6385bf` |
| `NLA/Proofs/MF03/Finite15.lean` | `1520e0c1454ddb999e334595549b5e12f41a2e1374c5cd1037ae361ef2974aea` |
| `FINITE_RANGE_PRE_REVIEW.md` | `026f12f8ac3c180e482bbb05088c72c2c5d212650568b8350cb39f10db0cb814` |
| `FINITE_RANGE_INDEPENDENT_PRE_REVIEW.md` | `94680e8b833de254d6fd3a60824a0deea512f270dc0f9627c778fe23da9f510b` |
| `FINITE03_15_INDEPENDENT_REVIEW.md` | `0c6c1ba34fa14aede54f142909e3ae9740dcba8a6eedebe579a9170e10708949` |
| Independent `/private/tmp/mf03-finiterange-independent-audit.lean` | `fe4d63e6b57d7caf417d76be87a40945e394bee51508efac296631db6d4cba26` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |

Changed theorem, dependency, or frozen target bytes reopen the affected review.
