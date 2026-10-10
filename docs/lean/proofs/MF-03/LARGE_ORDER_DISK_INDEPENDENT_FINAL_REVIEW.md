# MF-03 conditional large-order disk bridge: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen source for aggregate import as a conditional large-order disk theorem. It does not construct a normalized pair, prove the coefficient hypothesis, or inhabit the frozen all-order `Target`.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/MF03/LargeOrderDisk.lean` | `0bd595d22ae9237d608cfe9bf1e521e3ca5869df83ea729e8862e98ef493c7ec` |
| Exact large-order disk contract | `f9bf647e49d63c47fdbd14b10a7c00775164efc5cf6ae0c61b79c1a9dfdb847f` |
| Independent mathematical/numerical pre-review | `18084abb4d779f2fd1179fbc50e3e933f023c44614c279cfcaef0b7549e92113` |
| Frozen `NLA.Statements.MF03` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| Separate imported audit `/private/tmp/mf03-largeorderdisk-independent-audit.lean` | `67ba05725904b9ae37caa400049fb72095423c8e4dc914fa3348a81acc4f27d6` |

The theorem has the reviewed exact signature: for every `m≥16`, every normalized Padé pair for the frozen factorial series, and every denominator coefficient `j=1,…,m` bounded by `S_m^j`, it proves nonvanishing and error at most two for **all complex** `z` with `‖z‖≤3`. It adds no reduced-pair, product-identity, or existence premise. The helper extracts the exact finite coefficient difference from the frozen Padé convolution, including `j=0`, then bounds its radius-three sum by a Cauchy product of the finite denominator absolute values and the factorial tail `waveAtThree−1`. The source separately proves summability of that factorial tail and uses no unproved cosine product identity.

The supplied coefficient bound yields the finite geometric estimate `T(1−3S_m)≤3S_m`. The existing cosine-tail theorem gives `6S_m<1/24` for `m≥16`; exact algebra gives `T<1` and `(1+T)(1−6S_m)≤1−T`. The existing rational margin `(waveAtThree−1)/(1−6S_m)≤2−13/6095` then proves the precise `Disk.lean` budget `N≤2(1−T)`. Its conclusion covers the closed boundary, with no numerical sampling.

The pinned Lean 4.33.1 direct module build passed. My separate imported LeanCert audit exited zero, checked the theorem's elaborated signature, reran `#assert_trust kernel`, and printed only `[propext, Classical.choice, Quot.sound]`. A frozen-source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape. Changed source bytes require a new review.

The infinite cosine product identity, all-order normalized Padé existence, Schur/tableau denominator coefficient bound, reduction to a pair at every order, and the universal all-order MF-03 Target remain open.
