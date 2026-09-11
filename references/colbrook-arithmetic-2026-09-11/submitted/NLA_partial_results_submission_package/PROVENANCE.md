# Provenance and review status

This is an AI-assisted research and reproducibility package prepared on 11 September 2026. It is not a peer-reviewed publication, and no human authorship or institutional affiliation is asserted. A person submitting it should review the mathematics and code, determine appropriate authorship and licensing, and supply an archival link for the final reviewed version.

The conversation included workspace restarts. Earlier reported computations were regenerated in the retained workspace; the final certificate files and retained logs, rather than unretained reports, are the evidentiary basis of this package. The current rebuild began at the UTC timestamp in `logs/rebuild_started.txt`. No claim of three uninterrupted hours of retained computation is made.

Generation used GCC 14.2.0 and Python 3.13.5 in the retained environment. Some exploratory binaries used `-march=native`; `build.sh` deliberately omits that flag for portability. Arithmetic results and coverage arguments do not rely on timings. `SHA256SUMS` records the final delivered bytes.

The search and the full-matrix verifier are separate implementations, but share a proved polarization identity. A different subset-dynamic-programming formula was also used to recompute the cofactor vectors for orders 21–28. The small-order tests compare arbitrary-precision subset DP, direct permutation sums through order 6, and the C++ checker; they also test false claims, malformed input, and multiple thread counts. These are cross-checks, not a claim of formal proof-assistant verification.

Original third-party papers and repository PDFs are not redistributed. References identify the primary sources used to formulate the questions and establish the previously cited range.

The consolidated logs `logs/final_full_matrix_checks.log` and `logs/final_range_checks.log` combine separately completed checks; they are explicitly labeled composite evidence, not a fictitious single execution. The former covers all orders 1–35 and the latter all orders 1–10. The completed order-35 search used seed 20260911, base attempt 3; its successful-search and complete-matrix logs are retained.
