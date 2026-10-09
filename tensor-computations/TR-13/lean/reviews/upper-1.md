# Independent component proof review: TR-13 upper bound

Reviewer: OpenAI Codex AI agent `/root/choose_algebra`.
Date: 28 September 2026.

**Verdict: PASS for the complete generic Vandermonde upper bound.** The reviewer
did not author the reviewed upper-bound files. This is an AI-agent component
review, not human review or a review of the complete assembled TR-13 theorem.
The reviewer authored other, disjoint lower-bound components and does not claim
independence for those components.

## Files read in full

| File | SHA-256 |
| --- | --- |
| `NLA/TR13/Prony.lean` | `c80589f9124cbfb5adf3fb50f93fefa6a14303e0e4f5849d67efe0e5c14ca810` |
| `NLA/TR13/PronyPolynomial.lean` | `cb800a6c18d7a23af8b54d1de9b6997909456bc85483bfbbe600173cab287ac8` |
| `NLA/TR13/PronyWitness.lean` | `47629f85085fce41da5856ca5f6e7f1844abec4f8a35e93fe0aa87bb3763f337` |
| `NLA/TR13/UpperPolynomial.lean` | `cc7d7d7928a6becf3410f5148f94bad8dc91b0684d887c945e38e944c4eaa7a1` |
| `NLA/TR13/Upper.lean` | `f02165febe8d37e531ba767e2bfdc3bd8467c68a39556e4e55b67bcb8867e8d9` |

## Mathematical checks

The proof produces actual `r`-term Vandermonde decompositions. Its conclusion
does not substitute border decompositions, approximation, or a result-assuming
genericity condition for the required upper bound.

The finite moment matrix determines a recurrence through Cramer's numerators.
Multiplying its determinant by the fixed-degree resultant of that recurrence
and its derivative gives an explicit polynomial condition. Nonvanishing implies
both an invertible moment matrix and a separable recurrence of exactly degree
`r`. Over the complex numbers, the latter has exactly `r` distinct roots. An
invertible Vandermonde system supplies coefficients matching the first `r`
moments, and strong induction using the two recurrences matches every supplied
moment through index `2*r-1`.

The nonzero-certificate argument covers both parities of the number of input
moments. Periodic moments have an invertible permutation moment matrix and
recurrence `X^r-1`, which is separable in characteristic zero. If one final
Prony moment lies beyond the input, the zero extension agrees with the periodic
witness at that index: `2*r-1` is not divisible by `r` for `r>=2`. Thus the
polynomial is proved nonzero after the zero-extension substitution; no
dominance or constructibility theorem is assumed without proof.

The resulting moment identity is transported entrywise to the actual Hankel
tensor. The chosen homogeneous Vandermonde coordinates are `(a,b)=(1,t_j)`,
so they are always admissible. Finite nodes suffice for this upper bound; the
definition continues to allow the point at infinity. The theorem covers all
parameters of the original problem; its unused oddness hypothesis merely
reflects that this upper bound holds more generally.

## Independent Lean check

Ran the pinned toolchain command

```text
lake env lean reviews/upper-1-check.lean
```

It exited successfully. The script imports the finished upper bound, checks its
full type, and prints axiom dependencies for `generic_vandermonde_upper`,
`prony_representation`, and `upperPolynomial_ne_zero`. All three depend only on
`propext`, `Classical.choice`, and `Quot.sound`; see `upper-1-check.log`.
The reviewed source files contain no `sorry`, custom `axiom`, `native_decide`,
`unsafe`, or import of `Challenge`.

The final assembly must still intersect this nonzero polynomial condition with
the lower-bound condition and prove nonemptiness of that intersection. This
component theorem intentionally supplies the upper condition and its actual
decompositions, leaving that separate obligation explicit.
