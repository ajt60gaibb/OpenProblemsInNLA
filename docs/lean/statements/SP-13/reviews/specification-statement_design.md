# SP-13: independent specification review

Reviewer: /root/statement_design, OpenAI Codex AI agent. Date: 2026-09-28.
Verdict: **approve**, bound to the exact input bytes below.

## Fidelity reasoning

1. The complete dependent complex matrix sequences range over all finite sizes. Inclusion of n=0 adds only an irrelevant initial value; the empty Hermitian condition is automatic and both limits are at infinity.

2. Hermitian H is literal conjugate symmetry, while E and H+E have no added normality or uniform spectral bound. The single norm premise remains the full sum of all complex Euclidean singular values divided by n tending to zero.

3. Characteristic-polynomial roots form a multiset, retaining algebraic multiplicity including repeated zeros. A monic degree-n characteristic polynomial over the algebraically closed complex numbers has n roots counted this way. The normalized empirical functional is exactly the canonical one.

4. The class of tests remains every complex-valued continuous compactly supported function on the complex plane. The limit and integral both take complex values; there is no restriction to real-valued tests, smoothness, positivity or the real axis.

5. The revised symbol domain uses AEMeasurable under restricted Lebesgue measure rather than globally Borel measurable. This covers all original interval-measurable symbols and null-set modifications. Conversely an a.e.-measurable representative has the same integrals, so the apparent extension adds no distributional target.

6. The real symbol is embedded into Complex before F is applied. Values outside [0,1] are unused, and endpoint choices are irrelevant under Lebesgue measure. No boundedness or integrability of f itself is added; compactly supported continuous F is bounded and its composition is integrable on this finite measure space.

7. The same f occurs in both distribution predicates, and each predicate separately quantifies every permitted F. This correctly transports the complete limiting spectral distribution, without replacing it by individual eigenvalue matching or any known stronger perturbation hypothesis.

8. The full canonical README and byte-identical ORIGINAL were read, including target, definitions, resolution and preserved historical material. This specification approval is independent of the author /root and precedes implementation.

## Bound inputs

- docs/lean/statements/SP-13/NUMERICAL_TARGETS.md: 5f10905d6e0acfc2469a470321b310038e8d30ddb66d58bdf4b560b733fa7e60
- docs/lean/statements/SP-13/ORIGINAL.md: 3db39d15a2d3879c0e72a983dd78197bcc8b99ac256a07fcaeee5b6f0962a57a
- eigenvalues-and-inverse-problems/SP-13/README.md: 3db39d15a2d3879c0e72a983dd78197bcc8b99ac256a07fcaeee5b6f0962a57a

## Limits

Independent mathematical specification review only. No final SP13 Lean implementation or imported API behavior is certified by this report; roots multiplicities, Euclidean singular values and integral/limit meanings must be checked at final boundary review. No proof of the catalog target is claimed.
