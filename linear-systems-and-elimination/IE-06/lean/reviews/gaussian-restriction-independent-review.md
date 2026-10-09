# Independent source and mathematical review

Reviewed `NLA/IE06/GaussianRestriction.lean`, SHA-256 `05684a5622e0862df037fdbe42490799f5e9e7fcde741ce43fa9184152145c85`.

Independent review by /root of the frozen implementation by /root/source_statement_author. The actual measure is (gamma K)^(-1) times gamma restricted to K. Positive mass and probability finiteness justify cancellation. The completed square uses y+t v and exactly exp(t^2 sum(v_i^2)/2), with the corresponding translated preimage of K. Translation invariance is applied to Lebesgue density, not asserted for Gaussian measure. Anderson is proved in GaussianShift, not an input hypothesis. Full Gaussian exponential integrability implies restricted integrability before real-integral comparison. The resulting directional sub-Gaussian property and quadratic tail use the actual normalized restriction and have precisely (2+4x)F^2 and exp(-x), including x=0 and zero matrix. Approved exact statement and proof; this is not yet the adaptive GEPP conditioning law.

Compilation is recorded separately; this review does not claim Linux replay or the complete IE-06 theorem.
