# SP-14 scalar Schur power comparisons: independent final review

**Source author:** `/root/sp14_base_proof`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE this scalar partial gate for aggregate import. Weighted kernel Schur sums and the frozen SP-14 Target remain open.

The exact mathematical and indexing contract `ENDPOINT_WEIGHTED_SCHUR_PRE_REVIEW.md` was independently approved before implementation at SHA-256 `0433186b4e5af5637f31ebc752e13b4f545a5639a0fa4e4a547e9ff8ce205c21`. The frozen source `lean-statements/NLA/Proofs/SP14/EndpointWeightedSchur.lean` is SHA-256 `3f5e3bdcf912d1b38f2719ad9af1d647df69e987809d136c4865b892e0dbfccb`.

I read the complete source. It proves the exact finite bound `∑_(n=1)^N n^(−r) ≤ 1+N^(1−r)/(1−r)` for every `0<r<1`, `N≥1`, keeping the first term and comparing the rest with the integral of the antitone function. It also proves `∑_(n>N)n^(−r−1)≤N^(−r)/r` for every `r>0`, `N≥1`, with the strict lower tail index `N+1`. The continuous integral calculations use exact real powers; there is no floating-point computation. The source has no proof escapes or new axioms.

The pinned Lean 4.33.1 direct build passed. A separate imported audit `/private/tmp/sp14-endpoint-weighted-schur-power-independent-audit.lean` (SHA-256 `126bb5bd3c2925e300092b0388a4b12ffa6bdeb92be5da27c7deb626310a5c31`) checked exact public signatures and two `#assert_trust kernel` directives. Each `#print axioms` returned only `[propext, Classical.choice, Quot.sound]`. The aggregate build is recorded in PR verification after import.

These scalar comparisons alone do not establish either actual weighted row or column sum, finite Schur inequalities, the infinite-dimensional operator estimate, or the full negative Target.
