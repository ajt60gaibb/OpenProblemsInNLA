# Independent scalar-recursion review

Reviewer `/root`, independently of author `/root/source_statement_author`.
Reviewed `NLA/IE06/ScalarRecurrence.lean`, SHA-256
`f5936aa79c56e65f5bc3b238be3a103fed223048e0fccb6baf5d9edc683ec81f`.
The specialized route was independently approved before implementation in the
full-proof specification and its coordinator review.

The finite sum uses n terms, but no tail is lost: a positive starting index has
orbit at least d+i, so the term at n and all later terms vanish. This justifies
the exact cost recurrence. Monotonicity compares positive starting indices;
no unproved ordering of a stopping-time definition is used. The reciprocal
sum bound follows already from growth by at least a factor two, while the
actual step grows by at least one hundred.

For J=ceil(sqrt(log n)), log n≥256 gives J≥16. The first J steps reach at least
100 log n; the next J quadratic steps reach log(n) times 100^(2^J).
The elementary inequalities 2^J≥J²≥log n and log 100≥1 suffice to reach n.
The finite nonzero-term count is at most 2J, and the reciprocal contribution
at most 2 sqrt(log n). The ceiling slack is absorbed within the stated bound
6 sqrt(log n). No numerical evaluation of an enormous cutoff occurs.

The profile has the exact required recurrence and positive values at positive
dimensions/indices. Its ratio to d is monotone because the cost is antitone
and D≥0. The upper step/loss estimates retain their positivity hypotheses.
Every numerical inequality and recurrence is proved in Lean; there are no
probabilistic hypotheses hidden in this module. This is a sufficient scalar
route for the original subpower-loss target, not a claimed proof of the
stronger arbitrary-r logarithm-of-logarithm estimate in the source.

Mathematical and statement review: approved. Complete probabilistic assembly
still requires the actual spectral extension and initial Gaussian estimates.
