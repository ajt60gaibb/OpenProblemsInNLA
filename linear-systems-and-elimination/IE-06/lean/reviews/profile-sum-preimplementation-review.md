# Profile to retained inverse sum: preimplementation contract

Coordinator /root approved this exact contract before implementation; the
independent mathematical review agent reviewed the source-to-index mapping.

For an actual t-by-t real matrix T, natural r≥1, and a function g:Nat→Real,
assume g(r)>0, g(r)/r≤g(d)/d for each r≤d<t, and
g(d)≤Spectral.singularValue T (t-d-1) for each r≤d<t.
Then TruncatedInverse.sigmaInvSum T r≤2*r/g(r)^2. If t≤r the left side is
exactly zero. In the nonempty case, the retained index i=0,...,t-r-1
corresponds bijectively to d=t-i-1=r,...,t-1, so the final retained original
singular value is the source one-based sigma_(t-r), not the opposite end.
The positive ratio lower bound first proves all retained singular values
strictly positive; totalized zero inverse is never used in a comparison.

The scalar proof uses d⁻²≤2*(d⁻¹-(d+1)⁻¹) for natural d≥1, telescopes the
finite sum from r to t-1, and drops the nonnegative endpoint term. No infinite
sum or numerical computation is needed. A specialization takes g to the
existing ScalarRecurrence.profile and obtains its hypotheses from its proved
positivity and monotone-ratio theorems. No spectral lower bound is assumed
without an explicit theorem hypothesis, and this deterministic implication
makes no new probabilistic claim. The coordinator will review the code.

Implementation completed: `NLA/IE06/ProfileSum.lean`, SHA-256
`90a9ac674a1b98065cd651d252195bbf2f5345687135d54847db79bc311a4825`.
All seven local declarations have kernel-policy checks and printed foundational
axioms only. Local pinned-runtime receipt and log: `reviews/profile-sum/`.
The coordinator will independently review the frozen source.
