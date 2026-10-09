# RA-04: independent specification review

Reviewer: /root/statement_design (OpenAI Codex AI agent), 2026-09-28.
Verdict: **approve** for the bound specification bytes.

## Fidelity reasoning

1. The complete retained canonical question and archived report Section 1 agree with the proposed single absolute C, all rectangular real inputs, 1<=b<=k, t=ceil(k/b), m=bt<=rank(A), positive b-step gap, and both epsilon and delta in (0,1/2). The exact ceiling retains the factor 2 inside log(2/Delta) and has no added logarithmic dimension factor.

2. Zero-based sigma(A,k) and lambda(A,k) are exactly the one-based sigma_(k+1) and its square. Gap indices 0<=i<m-b cover every original term, all denominators are positive by m<=rank(A), and the empty minimum remains exactly one. Frobenius tail uses all finite singular values from index k onward and spectral tail is sigma(A,k), with no extra squaring of the requested error.

3. The only randomness is the actual finite independent N(0,1) product for G. The subspace is the real span of (AA^T)^j G for exactly 0<=j<q. Orthogonal Z with exactly that column span is an actual basis, including exceptional lower dimensional draws; no full-rank Gaussian promise removes failures.

4. The explicit B times top-k right-eigenspace projector is a complete SVD truncation of B=Z^T A. Orthogonal full V, nonnegative antitone squared singular values and exact reconstruction of B^T B cover sign, repeated, and zero singular values, rather than selected favorable vectors. Such a V exists for every real rectangular B.

5. The universal basis and tie convention is supported by the archived report equation (1.2), which expressly permits any orthonormal Z, and its unrestricted truncated-SVD and ordered-right-vector formulation. Section 7 applies its deterministic good-start theorem on a single event independent of these choices. Universal W retains every right spectral decomposition of the actual output. This review accepts the standard arbitrary-valid-choice algorithm convention, not a claim that an arbitrary favorable-selection formulation would be equivalent.

6. Both approximation norms and all ordered right-vector energies are conjoined inside the same success event for one G and all legal output choices. Probability is per input; only C is globally chosen. Operator norm is the actual Euclidean continuous-linear-map norm, and the vector energy is the complete sum of squared entries.

7. Full spectral decompositions and an orthonormal basis of the finite Krylov space always exist, so the universal predicates do not become vacuous by omitting output witnesses. Report Section 7 handles rank(A)=k and zero optimal tail by exact range recovery, with q>=t+1; the specification retains this case, nondivisible k/b, t=1, and every tie allowed by the b-step gap.

8. The source supplementary raw Krylov conditioning conjecture, finite precision and illustrative proof constant 80 C0+4 are correctly excluded from this existential-constant original target. No proof of the solved theorem is claimed by defining its statement.

## Bound inputs

- docs/lean/statements/RA-04/NUMERICAL_TARGETS.md: b274c4e9a2d719dd02586a8f4345d877917f30fcf1349fca584ae54f02643204
- docs/lean/statements/RA-04/ORIGINAL.md: a92ba711df188b40f7eba9320f956b53a72b7c61bb09aee5b72f91832027116e
- docs/lean/statements/RA-04/source-lock.json: 79d353ea0e2aefc8053b9062c5e696f851b79d6563c1ac69a64fa292b17f11f4
- randomized-and-low-rank-approximation/RA-04/README.md: a92ba711df188b40f7eba9320f956b53a72b7c61bb09aee5b72f91832027116e
- randomized-and-low-rank-approximation/RA-04/problem.tex: 3d3ec62321331ac17f2f94ce7b595bf52b9b44493db0fd42bfb89ea3bd2be4bc
- references/holden-ra04-full-proof-2026-09-13/STATEMENT_CORRESPONDENCE.md: 6ad298298f05990a16368018b5032905bd1540517f011f442570b976fd1fb50a
- references/holden-ra04-full-proof-2026-09-13/src/report.tex: 3d5d93cdfe457a54429ee169c46e0be623d77e9338c3af35efb9d825afe4fe41

## Limits

Independent AI-agent preimplementation specification review. Reviewer /root/statement_design did not author this specification. The full canonical page and cited archived source were inspected and source locks checked; this report approves mathematical/model correspondence only. No new Lean implementation, target proof, executable solver, or numerical certificate is approved. Final source/import/pin and actual kernel/frozen-identity reviews remain required.
