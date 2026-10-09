# MF-03: independent specification review

Reviewer: /root/statement_design (OpenAI Codex AI agent), independent of author /root.
Date: 2026-09-28. Phase: specification. Verdict: **approve**.
No mathematical changes requested for these exact bytes.

## Fidelity and equivalence checks

1. The coefficient a_j=1/(2j)! is exactly the entire cosh-square-root series without choosing a square-root branch. The convolution coefficient formula uses every i from 0 to j and every j<=2m, exactly vanishing through degree 2m in Qf-P.

2. The degrees are each at most m and Q(0)=1. For m>=1, using natDegree for the zero polynomial does not add cases: the j=0 coefficient equation forces P(0)=1, while Q is already nonzero.

3. The no-pole assertion is correctly required of reduced coprime numerator/denominator pairs. At a root of a coprime denominator the numerator cannot also vanish, so denominator nonvanishing is equivalent to absence of a pole. Imposing this on every unreduced representative could add removable-factor constraints, which the specification explicitly avoids.

4. Cancelling a common polynomial factor preserves approximation order: because Q(0)=1 the factor is nonzero at zero, so it is a unit in the local Taylor series; division preserves the order of Qf-P. Rescaling the cancelled pair restores Q(0)=1 and cannot increase degrees.

5. Any two normalized admissible pairs determine the same rational function: Q2(Q1f-P1)-Q1(Q2f-P2) vanishes through 2m, so P1Q2-P2Q1, of degree at most 2m, is zero. Thus universal quantification over reduced representatives is the original unique rational approximant.

6. The explicit existence conjunct prevents an empty class of admissible pairs from making the bound vacuous, faithfully expressing the source presupposition that the diagonal approximant exists at every m. It is not an assumed axiom.

7. All orders m>=1, every complex point on the closed disk |z|<=3, and weak bound <=2 remain. No m<=20, rational-z, real-coefficient, strict-bound or pole-location strengthening is introduced.

8. Complete ORIGINAL.md is byte-identical to the canonical README; permanent ID, full problem statement, resolution attribution and historical context are retained.

## Reviewed inputs

- docs/lean/statements/MF-03/NUMERICAL_TARGETS.md: 7330918bbef9002e38a2d38cd1b019d1170a707e3b8c1e4dfcb18e9b4133dd28
- docs/lean/statements/MF-03/ORIGINAL.md: 57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a
- matrix-functions-and-stability/MF-03/README.md: 57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a

## Limits

Independent AI-agent preimplementation specification fidelity review only. This approves these mathematical definitions and target correspondence, not any subsequent Lean implementation, proof of the target, cited-paper proof audit or kernel/Comparator run.
