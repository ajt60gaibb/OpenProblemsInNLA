# MF-03 orders 3–15: independent finite-certificate review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026. **Verdict:** APPROVE the 13 frozen `Finite03.lean` through `Finite15.lean` modules as exact normalized Padé witnesses with full closed-complex-disk pole-free error bounds at their respective orders. This is a finite **partial** result; these modules establish neither reduced-pair existence nor the all-order MF-03 `Target`.

## Exact mathematical and numerical audit

For each `m=3,…,15`, the private `P_m,Q_m : Polynomial ℂ` use `Polynomial.ofFn (m+1)` with every rational coefficient copied exactly from the corresponding `m` record of `wave_kernel_finite_certificate.json`. I independently parsed the Lean lists as fractions and compared every `P` and `Q` coefficient with that record; the repeated lists in the degree proofs match the definitions. Both constant coefficients equal one, and the source proves `P_m.natDegree≤m`, `Q_m.natDegree≤m`, and `Q_m.eval 0=1`.

An independent exact-fraction computation checked **every** Padé convolution index `j=0,…,2m` against the frozen `NormalizedPadeRepresentation` formula: `Σ_{i=0}^j q_i/(2(j−i))! = p_j`, with `p_j=0` above degree `m`. There are no sampled or floating-point equations. Each Lean `finiteXX_normalized` theorem quantifies over every `j≤2m` and dispatches those finite cases with exact `norm_num` proofs.

For each pair I recomputed `B=Σ_{i=0}^m |q_i|3^i`, `T=B−1`, `N=Σ_{i=0}^m |p_i−q_i|3^i`, `2(1−T)−N`, and `N/(2−B)` in exact fractions. Every value equals the JSON record, every `B<2`, and every two-bound slack is **strictly positive**. The Lean `finiteXX_disk` theorems discharge the exact `T<1` and `N≤2(1−T)` premises of the independently reviewed `disk_bound_of_coefficient_tail`; their conclusions give `Q_m.eval z≠0` and `‖1−P_m.eval z/Q_m.eval z‖≤2` for **every complex** `z` with `‖z‖≤3`, including the boundary. The weak constant two and radius three match the frozen Target. The exact JSON `bound=N/(2−B)` is sharper at these orders but is not substituted for the canonical target.

The file-by-file binding is:

| Order | Lean source SHA-256 | Checked coefficient indices | Padé indices | JSON budgets |
| --- | --- | --- | --- | --- |
| 03 | `45ad66cf9ea996dd5ce1a8de884659fac739215c9db2f701ff9ae7e9a66af30b` | `0…3` | `0…6` | exact; slack > 0 |
| 04 | `97baa4b71888cb97a6116e26a1d5f1a7d631611b0969a68e80b7f325a5287ee7` | `0…4` | `0…8` | exact; slack > 0 |
| 05 | `bc6d2219c84438846b9b6c081b2d9332931c15e9047781560b713a1611545181` | `0…5` | `0…10` | exact; slack > 0 |
| 06 | `d8acae03b23c3bebd8309ae9da25b2ac261ba52e5fea41cbfa56ad12b6313a4c` | `0…6` | `0…12` | exact; slack > 0 |
| 07 | `5938ae3bf906a1835b0cce737ce5a427465a1255ebd43c757c821248b57a8e21` | `0…7` | `0…14` | exact; slack > 0 |
| 08 | `ee431488e3d090efdc4db47fdbe76ee96fdf388a92445f1fda719da78a8e2979` | `0…8` | `0…16` | exact; slack > 0 |
| 09 | `5beb2f01343aa7aa5bdf22242498181aa72889b6b92a1fb99f44a42cb9d5c871` | `0…9` | `0…18` | exact; slack > 0 |
| 10 | `54742c4fddd08254768482620523e9e141ba49fabaf9344ee7247d66b127c835` | `0…10` | `0…20` | exact; slack > 0 |
| 11 | `83f555893cc34ff6a8e5701e1a722b751aa0b3eeab362e2736d0f45b8484a6c4` | `0…11` | `0…22` | exact; slack > 0 |
| 12 | `3304258460f2bb9fbebb792cb42642c72566fd706facfae56bef5a5d5051fa2b` | `0…12` | `0…24` | exact; slack > 0 |
| 13 | `6b2ab289fcf4ed57f72fb3707513338fa984bb6ac920d4968a7dc660b7dacd91` | `0…13` | `0…26` | exact; slack > 0 |
| 14 | `b28d1ec6b0422559133253607384e195dc388c5d829625a86dfd83d28e6385bf` | `0…14` | `0…28` | exact; slack > 0 |
| 15 | `1520e0c1454ddb999e334595549b5e12f41a2e1374c5cd1037ae361ef2974aea` | `0…15` | `0…30` | exact; slack > 0 |

## Kernel and scope

After the author's sequential pinned builds, my separate audit imported all 13 frozen modules and ran `#assert_trust kernel` and `#print axioms` on each `finiteXX_normalized` and `finiteXX_disk`: all **26** passed. Every transitive axiom list is exactly `[propext, Classical.choice, Quot.sound]`. A scan of all 13 sources found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

The private rational pairs are normalized and have disk certificates. None of these modules proves `IsCoprime P_m Q_m`, a reduced normalized pair exists, or the universal disk clause for every reduced representative. The separate Transport lemma is conditional on a supplied reduced pair. Orders `m≥16` and the full all-order existence argument remain outside this review.

## Other SHA-256 bindings

| Input | SHA-256 |
| --- | --- |
| Frozen `NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| Reviewed `NLA/Proofs/MF03/Disk.lean` | `c7ced478264defa6a8365df21c2cb3d861adc18c37d67c793c3336df14d7f53a` |
| Exact `wave_kernel_finite_certificate.json` | `6d000c2b0b37acac1fca07bac239534d68177213da56f9c34aa5a5105c9cbaa8` |
| Source manuscript `MF-03.tex` | `312e90a79405a6cf0b116d5e3cc402a242107104f56b5abf542a18ff36247b` |
| Independent exact-fraction `/private/tmp/mf03-finite03-15-independent-audit.py` | `2384a10ef40dca9ea086e50dc566f6250d9a98b8a1a9ce435ed8b3f44cd6953d` |
| Independent `/private/tmp/mf03-finite03-15-independent-kernel-audit.lean` | `0fcdc95835208f0f007530fae3e0bfa3aeb1b73848668c19a579a0d4d8b07854` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |

Any change in the certificate, theorem source, or frozen target requires renewed review of the affected claim.
