# MF-03 disk lemma: independent partial-proof review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026. **Verdict:** APPROVE the frozen `Disk.lean` as a conditional closed-disk coefficient-budget lemma. It is **not** a proof of `NLA.Statements.MF03.Target` and certifies no Padé order by itself.

The exact canonical target, approved in [STATEMENT_INDEPENDENT_REVIEW.md](STATEMENT_INDEPENDENT_REVIEW.md), asks for every `m≥1` that a **reduced normalized** diagonal Padé pair exists and that **every** such pair has no pole and error at most two on the closed complex disk `‖z‖≤3`. The manuscript's finite certificates cover orders `1,…,15` with rational polynomials and two aggregate inequalities; its separate analytic argument treats `m≥16`. `Disk.lean` addresses only the geometric implication from those aggregate inequalities to a disk bound.

`norm_eval_le_coeff_radius` correctly bounds a degree-at-most-`m` complex polynomial on `‖z‖≤R` by `Σ_{j=0}^m ‖coeff_j‖ R^j`. The assumed disk point implies `R≥0`, so the real-power monotonicity step is sound even though no separate `R≥0` premise is written. `norm_eval_sub_one_le_tail` uses `Q.coeff 0=1` to bound `‖Q(z)−1‖` by the **nonconstant** terms `j=1,…,m`. Both sum ranges include their correct endpoints.

The main `disk_bound_of_coefficient_tail` assumes `P.natDegree,Q.natDegree≤m`, `Q.coeff 0=1`, and the exact budgets

```text
T = Σ_{j=1}^m ‖Q.coeff j‖ 3^j < 1,
N = Σ_{j=0}^m ‖P.coeff j−Q.coeff j‖ 3^j ≤ 2(1−T).
```

It concludes, for **every complex** `z` with `‖z‖≤3`, both `Q.eval z≠0` and `‖1−P.eval z/Q.eval z‖≤2`. The reverse triangle inequality gives `‖Q(z)‖≥1−T>0`; the coefficient norm bound gives `‖P(z)−Q(z)‖≤N`; dividing by the positive denominator yields the weak constant-two bound, including the boundary case required at `m=1,z=3`. The proof uses exact polynomial identities and inequalities, with no numerical sampling or floating point.

This is exactly the manuscript certificate's disk step: its `B_m=Σ_{j=0}^m |q_{m,j}|3^j` has constant term `|q_{m,0}|=1`, so `B_m=1+T`; hence `B_m<2` is `T<1`, and `N_m≤2(2−B_m)` is `N≤2(1−T)`. The normalized Target says `Q.eval 0=1`, mathematically equivalent to this lemma's `Q.coeff 0=1`. The Python certificate verifier still passes all 15 records, but this Lean lemma does **not** import or check those rational records. It also does not prove Padé coefficient identities, existence, coprimeness/reduction, uniqueness or transport to every reduced pair, the all-order denominator estimate, or the analytic `m≥16` argument. Its theorem quantifies over arbitrary `m`, including zero, only **conditional on** the displayed budgets; that stronger parameter range must not be reported as the full all-order Target.

I ran `lake build NLA.Proofs.MF03.Disk`, direct `lake env lean NLA/Proofs/MF03/Disk.lean`, and a separate audit importing the module. All exited zero under pinned Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. The audit confirmed all three declarations are `.thmInfo` proof constants and passed `#assert_trust kernel` for each with transitive axioms exactly `[propext, Classical.choice, Quot.sound]`. A source scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`. The standard-library finite-certificate `--verify` command independently exited zero; that result remains source evidence, not Lean proof of the certificate data.

## SHA-256 of reviewed inputs

| Input | SHA-256 |
| --- | --- |
| Canonical `MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| Frozen `NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| **`NLA/Proofs/MF03/Disk.lean`** | **`c7ced478264defa6a8365df21c2cb3d861adc18c37d67c793c3336df14d7f53a`** |
| `STATEMENT_REVIEW.md` | `7c7d7c8de42fdf16aff0365dbcaf89586fdf87cd612c6ebab46cfa3b51e0ab41` |
| `STATEMENT_INDEPENDENT_REVIEW.md` | `dff7af4c1fc3b352ef9afbaf422bf644cb77118297b81c71b6793baf080ef2e5` |
| Manuscript `MF-03.tex` | `312e90a79405a6cf0b116d5e3cc402a242107104f56b5abf542a18ff36247b` |
| `wave_kernel_finite_certificate.json` | `6d000c2b0b37acac1fca07bac239534d68177213da56f9c34aa5a5105c9cbaa8` |
| `wave_kernel_certificate.py` | `73587f8a4a5afd12bd6f33ae9ffb5b85c9388831cf152b48a4c64595f84c3155` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| Independent `/private/tmp/mf03-disk-independent-audit.lean` | `af850bd8b1b1ee69d904c25cf1e5f3dbe332f4f3f718b7ed19f03c9902b88272` |

Any change to the lemma or target bytes requires renewed review of the affected claim.
