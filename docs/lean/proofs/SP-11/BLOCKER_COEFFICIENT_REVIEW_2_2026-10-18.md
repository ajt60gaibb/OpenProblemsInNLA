# Independent review 2: ordinary blockers and exact Gram coefficient

Reviewer: `/root/solved_inventory`, independent AI agent, 18 October 2026.
Verdict: **APPROVE OrdinaryBlockers and GramCoefficient at the hashes below, within their stated support scope. No blockers found. No unconditional SP-11 proof or status promotion is certified.** I did not author or edit either source.

I read both complete modules and independently recompiled their unchanged bytes with the pinned Lean runner. [Actual command results and hashes](blocker-coefficient-review-2-evidence-2026-10-18/result.json) and individual logs record two successful fresh runs. LeanCert kernel assertions pass and printed closures contain only `propext`, `Classical.choice`, `Quot.sound`. These are local development checks, not isolated Linux Comparator acceptance.

OrdinaryBlockers selects the actual earlier sibling at every smaller canonical slot. Strictly increasing original labels make that witness an earlier class; injective actual sibling outputs make its output distinct. The source does not assume that arbitrary sibling lists have those properties. Its tree specialization derives the label condition from actual HasChildLabels data and derives child-output injectivity from the parent's injective incident tuple, through the exact input/child-output conduit identity. The hbest slot-color premise is explicit, so the module does not pretend to handle the later top root before the augmented insertion correspondence has been supplied. Zero slots correctly have an empty smaller-color obligation.

GramCoefficient rewrites the actual polynomialLSS Gram polynomial using the proved paired-garden signed monomial expansion. Its uniqueness premise ranges over the entire actual finite paired-coloring type and excludes only zero-sign summands. It permits zero contributions sharing the distinguished exponent, which is mathematically correct. The coefficient is exactly the best coloring's actual sign product. If that coefficient is nonzero, zero polynomial equality would force it to vanish, yielding the claimed nonzero polynomial. There is no sampled evaluation, favorable subset of colorings, or independent-occurrence replacement.

Both proofs correctly retain their remaining premises. The canonical pair's admissibility/nonzero coefficient and complete graph-specific uniqueness must still be supplied before GramCoefficient yields all required diagonal/edge nonvanishing. The full frozen Target and final independent scope/CI evidence remain separate gates. Canonical pages, IDs, originals, reviewed target definitions and earlier frozen module bytes were not changed.

| Reviewed source | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP11/OrdinaryBlockers.lean` | `751ec7b20b1ffd73c89436311b9db7f2762acd92da45fbd7a18af55666c64b8d` |
| `lean-statements/NLA/Proofs/SP11/GramCoefficient.lean` | `9860b3c5ed250276225be71a779afc049ca5462ee00f37c97392bceded145a89` |
