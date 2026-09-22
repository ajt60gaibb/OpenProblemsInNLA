# IE22 independent partial module review

**Verdict: APPROVE** the three hash-bound modules below. No mathematical or statement-correspondence defects found.

Reviewer: AI agent `/root/infrastructure_audit`. I authored none of SupremumSemantics, SphericalRealization or DeterministicSchedule and did not edit their proof sources. I did author separate IE22 Gaussian modules and some unchanged reused IE21 modules. This is an independent review of these three modules only, not an independent final whole-package review.

## Frozen inputs

- `SupremumSemantics.lean`: `122998d2cb98c0eac3d95eceb137480fee755e365ebc2fe4aa271e9207beb884`
- `SphericalRealization.lean`: `77f3361581fb01b268394d0355ae3925555926ad7039212a7f5e0d807fa90d72`
- `DeterministicSchedule.lean`: `f8685f8868e77dbe7e9647bb56c6de0a3dbfc483b81ea8cd093a43dd7bc17fae`

I read each complete proof and compared it with the canonical IE-22 page, the complete retained IE-21–22 manuscript, frozen Definitions/NUMERICAL_TARGETS and the five exact Challenge signatures. The boundary remains byte-identical to the two-approved preproof freeze. The reused IE21 sources remain identical to their dependency receipt. No Challenge module is imported by these proofs.

## Mathematical findings

The supremum is the actual unsquared canonical statistic. The unit-row domain is the continuous image of a compact product of genuine Euclidean unit spheres; it is nonempty when n≥1. Continuity of the exact deletion minimum makes its value set compact, so its real supremum is finite and attained. The proof does not rely on empty/unbounded sSup defaults. A minimizing retained set/direction and Cauchy--Schwarz give the stated sqrt(n) bound. The final nonnegativity and squared identity quantify over every matrix, including matrices without unit rows, exactly as required. The floor-based retained row count and possible zero retained rows remain those of the unchanged IE21 minimum. The constant theorem uses the literal Gaussian integral and its established nonnegativity.

Spherical realization uses the actual normalized surface-row law's full unit-row support and the complete IE21 finite-size failure bound. If no literal unit-row matrix satisfied the normalized-deletion estimate, the bad set would have probability at least one, contradicting the strict finiteFailure<1 hypothesis. This proves a deterministic matrix existential with the required numerator normalization; it does not substitute only a ratio estimate. The near-extremizer proof applies to every positive integer sequence with n→∞ and m/n→∞. IE21's exact aspect schedule makes the numerator error smaller than epsilon squared. The nonnegative squared-statistic identity then gives the strict unsquared lower bound, separately handling sharpConstant<epsilon and sharpConstant≥epsilon (including equality). No additional growth condition or coupling across dimensions is introduced.

The schedule uses exactly floor(n^(2/3)) and n^(−1/6), not replacements. Exact rpow identities establish n*delta^6=1 and n^(2/3)*delta^4=1 for n≥1. The floor inequalities yield r≥1, r<n, r≤n*delta², 1/(r+1)≤delta^4 and n−r≥n/2 once delta≤1/2. All reciprocal denominators are proved positive. The three original failure terms are bounded by (6+4L²+8L)*delta. The deterministic bound minus h is at most 16*delta, using 0≤h≤1 and (1−delta)²≥1/4. Consequently C=22+4L²+8L>0 controls both errors, and C*delta→0 gives strict eventual admissibility. The constants depend only on theta through L=2/(1−theta), and neither m nor A enters the schedule.

## Independent verification and limits

I used separate new external build directories, rebuilt Definitions and each reviewed module from source, and checked five example types extracted verbatim from the frozen Challenge declarations. All seven compilation commands exited zero, without warnings or errors. All 17 public theorem/lemma axiom closures were printed and contained only propext, Classical.choice and Quot.sound. Source hashes were checked before and after each build. Full commands, exact type tests, logs and receipts are in `supremum-spherical-referee-infrastructure-evidence/` and `schedule-referee-infrastructure-evidence/`. The final review receipt binds those artifacts and the original canonical/manuscript inputs.

The local builds reused pinned third-party caches and the unchanged previously verified IE21 dependency cache; their provenance and binary/source-authentication limits are disclosed in the receipts. This review does not certify a complete IE22 package, authentic Linux LeanCert/Comparator execution, final status promotion or publication. Those require the campaign's separate complete-input checks and nonauthor final referees.
