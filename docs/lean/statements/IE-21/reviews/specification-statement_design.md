# IE-21: independent specification review

Reviewer: /root/statement_design (OpenAI Codex AI agent), 2026-09-28.
Verdict: **approve** for the bound specification bytes.

## Fidelity reasoning

1. OriginalLimitTarget independently retains the exact ratio convergence in probability, all theta in (0,1), and both growth conditions n->infinity and m/n->infinity. Full positive initial dimensions discard only irrelevant finite prefixes. No relation between their growth rates is added.

2. The finite product of the normalized actual Euclidean toSphere measure gives independent uniform sphere rows, including n=1. The pinned HaarToSphere API was checked: its mass is dimension times the cone volume, finite and nonzero on positive-dimensional Euclidean space. Unit support alone, deterministic independent rows, or a top measurable-space instance would not express this law.

3. The trimmed squared singular quantity is the infimum of the exact quadratic energy over all row subsets with floor(theta*m) elements and all Euclidean unit vectors. Compactness/finite subset arguments make this the actual minimum and preserve rank deficiency and empty retention. The denominator opSq is the genuine maximum quadratic energy and is positive for positive many unit rows.

4. The Gaussian mean/variance convention, positive exact quantile condition and normalized interval integral preserve the original h_theta. Quantifying all such a is faithful because the standard Gaussian symmetric quantile exists uniquely for every theta in (0,1). No approximation or arbitrary constant replaces it.

5. QuantitativeAnswerTarget is explicitly separated and credited as a stronger supplied answer to the source qualitative quantitative-bounds request. Combined Target is a conjunction, not a claim that the displayed original conjecture itself prescribed these numeric bounds. OriginalLimitTarget must stay separately exported and checked.

6. The manuscript Sections 4-5 were read directly. The exact constants 2,9,512,5,2, the n powers, L=2/(1-theta), L/m floor term, delta net term and (1-t) denominator match the source. Both error inequalities hold on the same covariance/net event; bounding the union of strict failures therefore needs the stated single B, not an extra factor or an intersection.

7. The quantitative parameter domain m>=1,n>=2,0<t<1,0<delta<1,0<eta<=(1-theta)/2 preserves the source restrictions. B may exceed one, and no such parameter choices are discarded.

8. The supplied growth calculation is valid: choosing u=32 sqrt(log Q/Q) gives the first base 9/Q^2 and the second bounded by 2 Q^(-2047.5), eventually both below one and tending to zero. Thus both growth conditions suffice without a hidden log(n) aspect-ratio restriction.

9. The old scaffold was inspected for its scope claims: SphericalRowLaw does give only sphere support plus independence, and the top matrix measurable-space instance is present. These old meanings are correctly excluded from the proposed concrete law.

10. Full canonical README and ORIGINAL agree byte-for-byte. The specification, original source, credited manuscript and old definition source are bound below; this review precedes any new implementation.

## Bound inputs

- docs/lean/statements/IE-21/NUMERICAL_TARGETS.md: 68cfc356391fa85cf41564afaac75feb5fdc428a211d96d71776fd6db057da08
- docs/lean/statements/IE-21/ORIGINAL.md: 71783a338942837a9c37bf2d50801484e711e55ee36a8da62d009bad518ae3ba
- linear-systems-and-elimination/IE-21/README.md: 71783a338942837a9c37bf2d50801484e711e55ee36a8da62d009bad518ae3ba
- linear-systems-and-elimination/IE-21/lean/Definitions.lean: da5fc6e89e278d81a6a92471706e80598833e29d387ea6361f5c69873fc7794e
- references/colbrook-recovered-2026-09-11/manuscripts/IE-21-22.tex: 31a1949c07f63408538f04e3803d90e8d3d0c3d1e47dc89a2ffa5a04ef4f3880
- references/colbrook-recovered-2026-09-11/verification/reviews/IE-21-22-review.md: d174419a6f71de369b7608a53b36dffa9cd815e3fd65a70d16457318cb68234d

## Limits

Independent AI-agent preimplementation mathematical/model specification review, independent of /root/infra_audit, its author. No final Lean API use, compilation, target theorem or numerical certificate is approved by this report. Final source/import/pin review remains required.
