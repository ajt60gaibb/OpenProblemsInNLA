# Aspect-schedule development evidence

Author: Codex AI root, 2026-09-22. The exact frozen `aspect_schedule` is implemented without new assumptions. Original analytic argument: Matthew J. Colbrook. Formalization credit: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology.

For Q=m/n and d=32 sqrt(log Q / Q), the proof establishes eventual admissibility, the exact identity m d²=1024 n log Q, and an eventual failure bound 7/Q. Both exponential terms are controlled for all n≥1. The elementary logarithmic limit gives d→0; n→∞ and Q→∞ imply m→∞, so each term in the reviewed ratio-error formula tends to zero and its denominator tends to one. No polynomial or logarithmic relative-growth restriction is imposed.

This is author development evidence only: the local sparse Lean 4.33.1 build and transitive axiom report passed with only propext, Classical.choice and Quot.sound. This does not substitute for independent proof review, actual Comparator, full LeanCert kernel assertions, authenticated reproducible Linux verification or completion of the other IE-21 targets. The unused positivity-of-m assumption is retained in the theorem signature (binder renamed `_hm`); it follows eventually from the stronger divergence assumptions for the limits used here.
