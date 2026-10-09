# IE-26 independent final Lean statement review

Reviewer: OpenAI Codex AI agent `/root`; verdict: approve. Author: `/root/statement_design`.

Frequency casts before subtraction, so the full signed spectrum is correct. Node and positive-sign exponential expressions use node rows/frequency columns. EvaluationMatrix is unnormalized; FourierMatrix multiplies by exactly reciprocal sqrt(2N+1). Interpolant applies the actual unnormalized matrix inverse to the full complex data, with no missing normalization factor.

LebesgueConstant uses the nonempty compact complex coordinate unit ball and whole closed real interval, retaining the continuum infinity norm and arbitrary complex data. The periodic continuous interpolant has the same essential and pointwise maximum. Distinct nodes under the existing weak shift bound and alpha<1/2 ensure both genuine inverses without a new determinant premise. InverseNorm uses the actual complex Euclidean continuous-linear-map norm of the normalized inverse.

FirstBound places its positive constant before N,alpha,shifts and retains the full rational expression and every 0<alpha<1/2. SecondBound places alpha first, then its positive constant before N,shifts, retaining 1/4<alpha<1/2 and the real exponent 4alpha-1 without a log factor. All endpoints, N>=2, weak admissibility and non-strict comparisons match. Target conjoins both statements.

Independently compiled the live and frozen sources, then fresh rfl equalities for FirstBound, SecondBound and Target. All pass using the pinned macOS Lean runtime and only the permitted three axioms. Source-fidelity review includes actual imported inverse, complex exponential, real power and Euclidean-map semantics. No correspondence theorem, bound or catalog truth is claimed proved by this work.

Local compilation evidence is separate from Linux Comparator verification.
