# IE-22 trimming threshold author handoff

All three frozen selected declarations are implemented: `bounded_trimming_threshold`, `threshold_lipschitz`, `threshold_grid`. This is an author report by AI agent `/root/ie21_final_fidelity`, who also drafted the IE-22 boundary; it is not independent review.

The first-moment/count argument proves that at least floor(theta*m) nonnegative observations lie below the literal L=2/(1-theta). It then reuses the unchanged IE-21 attained finite dual, including k=0 and tied values. The signed dual increment lies between minus and plus the threshold increment, proving the sharp Lipschitz constant1. The grid consists of i*delta for i<=floor(L/delta), includes0, stays inside[0,L], and actually satisfies card<=L/delta+1, which implies the exact frozen +2 target. No empirical quantile, sampling approximation, or conclusion premise is introduced.

The local stable run recompiles the new module and checks three complete Challenge signatures copied as examples without importing Challenge; each exported theorem has exactly propext, Classical.choice, Quot.sound. The source and audit compile with zero warnings. All four frozen statement files and all31 vendored IE-21 source hashes are checked by the build driver. Cached upstream dependencies and the previously built unchanged IE-21 modules are used; no authenticated Linux/LeanCert/Comparator completion is claimed. Independent review and the eventual complete-target gates remain required.

Helper APIs are `retainedRows_le_small_count` and the general signed-increment lemma `trimDual_increment`, useful for event assembly. No frozen boundary or vendored source was edited.
