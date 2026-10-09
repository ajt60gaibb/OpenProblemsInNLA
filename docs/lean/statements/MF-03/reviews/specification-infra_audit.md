# MF-03 independent preimplementation specification review

Reviewer: `/root/infra_audit`, an OpenAI Codex AI agent independent of the target specification author. Phase: specification. Verdict: **approve**.

I read the complete canonical README and exact specification and independently checked the proposed mathematical representation before any target Lean implementation. Infrastructure authorship does not make this reviewer an author of these problem specifications.

The original entire series has coefficient 1/(2j)!, and the proposed identities are exactly the convolution coefficient equations for Qf-P at every j=0,...,2m. Thus they express the order-2m+1 agreement without a square-root branch or an approximate disk evaluation. At j=0, Q(0)=1 forces P(0)=1.

Degree bounds at most m, normalization Q(0)=1, and coprimality describe reduced normalized representatives of the intended diagonal Pade rational function. Cancelling a common polynomial factor preserves the vanishing order because the factor is nonzero at zero; renormalizing the quotient denominator at zero preserves both degree bounds and all coefficient equations.

Two normalized solutions determine the same rational function: P1 Q2-P2 Q1 has degree at most 2m and a zero of order at least 2m+1, hence vanishes identically. Reduced denominators are therefore appropriate for the no-pole assertion; requiring arbitrary unreduced denominator nonvanishing would add an unintended condition, which this specification avoids.

The existence conjunct explicitly records the approximants presupposed by the source's for-each-order wording and prevents a vacuous universal over an empty representation set. For a reduced complex polynomial fraction, a denominator zero is a genuine pole because coprimality rules out a common zero. The proposed nonvanishing condition is therefore precisely the reduced-rational no-pole condition.

All positive orders, complex points in the closed disk of radius exactly 3, and the weak error bound 2 are retained. The specification adds neither the stronger strict bound for m>=2 nor a finite-order restriction. Complete ORIGINAL.md bytes match the canonical README.

This approval applies only to the input bytes below. It verifies statement fidelity, not truth of the conjecture or cited resolution, human peer review, a Lean boundary, or Linux Comparator execution. The implemented definitions still require independent boundary review.

- `matrix-functions-and-stability/MF-03/README.md`: `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a`
- `docs/lean/statements/MF-03/NUMERICAL_TARGETS.md`: `7330918bbef9002e38a2d38cd1b019d1170a707e3b8c1e4dfcb18e9b4133dd28`
- `docs/lean/statements/MF-03/ORIGINAL.md`: `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a`
