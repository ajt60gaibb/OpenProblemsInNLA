# RA-20 negative resolution from the maintainer audit

The initially proposed all-order formula in PR #111 is false at n=s=3. The permanent RA-20 ID, canonical path, complete dimension range and all four formulas are retained. The entry is Solved with an explicit negative resolution; no corrected formula or proof of the remaining cases is asserted.

- [Complete proof](../../../randomized-and-low-rank-approximation/RA-20/solution.md).
- [Independent agent reconstruction](independent-review.md).
- [Standard-library exact checker](verify_counterexample.py), run with `python3 verify_counterexample.py`.
- [Recorded exact output](exact-results.json).

The argument is generic, not merely a numerical witness: on the nonempty Zariski-open set of data with three nonzero off-diagonal coordinates, there are exactly three smooth, simple critical points. The source's Conjecture 5.6 and Table 7 give four. The counterexample was identified and separately reconstructed by multiple Codex agents; it was also checked by the integrating agent. This is automated-agent verification, not external human peer review or formal certification. No historical-priority claim is made.

Reviewed original PR head: `450ee69e20e54bb687240e01477cf95b0de61e0e`. Review date: 2026-09-11.
