# Independent pre-body mathematical statement review: MI27 inertia bridge

Reviewer: Codex agent `/root/new_math_nr01`, 19 September 2026. I did not
author the reviewed planning note, the shared NegativeCount source, or the
proposed helper bodies. This is an independent AI-agent mathematical review,
not external human peer review, Lean elaboration, kernel replay or Comparator.

**Verdict: PASS for the proposed mathematical statements and reduction.**

Exact reviewed planning note:
`development/MI27-C11-referee-a-v1/INERTIA-BRIDGE-OBLIGATION.md`, SHA256
`37f8e0da1e1f0ca98d70a7406bc023facb7c6cf7dcf06cccec19bc4ad7dd063e`.
The entire note was read. I also read the shared
`NLA/MI27/NegativeCount.lean` in that development directory to check the
actual strict-negative definition and the stated spectral-count interface.
Its source hash is recorded in the accompanying manifest.

## Rectangular cardinal inequality, including empty index types

The transported-form equality has the correct orientation and dimensions:
T maps C^n to C^m, b weights the input coordinates and a weights the output.
Let E_b be the coordinate subspace supported on b<0. Project T(E_b) onto
the negative a-coordinates. If a nonzero v in E_b were in this map's kernel,
the b-form would be strictly negative: every supported term is nonpositive
and some norm square is positive with a strictly negative weight. On the
right, all negative a-coordinates vanish and every remaining weight is
nonnegative. This contradicts hform. The map is complex linear and injective,
so its complex dimension inequality is exactly the proposed cardinal bound.

No positivity, nonzero-weight or nonsingularity assumption is missing.
If n=0, the negative-input space and left cardinal are zero. If m=0, the
right form is zero; hform forbids every negative input weight (test its
coordinate vector), so the left cardinal is also zero. If both are zero,
both sides are zero. Repeated and zero weights introduce no difficulty.

## Arbitrary-S congruence inequality

For N=S* M S, N is Hermitian for every S. Taking eigenvector unitaries U of M
and V of N, and T=U* S V, produces the transported diagonal-form identity
with a the eigenvalues of M and b those of N. The rectangular lemma gives
negative-count(N)<=negative-count(M), with strict-negative eigenvalues and
their multiplicities. Singularity of M or S is allowed. In particular S=0
gives count zero, and zero eigenvalues are never counted as negative.

The supplemental quadratic-spectral header has the correct conjugation:
coefficients are U* v, and the left side is the real part of v* M v.
It holds also at dimension zero; the matrix-count interface's hn>=1 is an
existing API restriction, not a new mathematical assumption on weights.

The shared CFC definition uses the strict step function x<0. Its displayed
spectral-count lemma identifies the real trace with the finite sum of those
indicators. Thus the proposed dimension argument matches the actual count,
rather than a trace congruence assertion, positivity assumption or a different
index convention. Finite-spectrum continuity is explicitly supplied in that
shared source; no global continuity of the discontinuous step function is
being presumed in the planning argument.

## Invertible-S equality

Apply the one-sided inequality first to (M,S), then to (N,S^{-1}). The second
congruence reduces exactly to M because S is a matrix-ring unit. Combining
the two inequalities gives equality. This does not require perturbing a
singular M or assuming its eigenvalues avoid zero. `IsUnit S` is the needed
matrix-invertibility hypothesis.

## Limits and implementation obligation

I approve these statements and the mathematical proof plan before new helper
bodies are authored. I did not check Lean syntax, imported API elaboration,
the body of a future inertia helper, the full C11 proof, or any compiler,
Comparator or GitHub result. Those checks remain separate. The implementation
must construct the stated linear map and hform; neither injectivity nor
inertia may be added as an extra hypothesis. This review changes no target
completion count and grants no publication approval.
