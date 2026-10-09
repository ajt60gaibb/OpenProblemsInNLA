# RA-05: independent specification review

Reviewer: /root/statement_design (OpenAI Codex AI agent), 2026-09-28.
Verdict: **approve** for the bound specification bytes.

## Fidelity reasoning

1. The complete canonical README retains two requests: joint worst-case size classification up to logarithms for each fixed real p>2, and the literal additive proposal. Classification explicitly states the credited resolved rate; OriginalAdditiveConjecture separately preserves the false subsidiary assertion, and NegativeAnswer negates its complete constant/input quantifier chain for every p>2. Target conjoins the classification and negative answer, never the false proposal.

2. The original-row strong coreset uses nonnegative arbitrary real weights, counts actual nonzero support rather than total mass or repeated copies, and requires one weight vector to work for every real subspace of dimension at most k. The proposed symmetric idempotent real projector with actual matrix rank<=k is exactly the corresponding orthogonal projector. It retains zero and all lower-dimensional subspaces.

3. The row residual A_i-A_i P is the original row action of I-P. Its finite sum-of-squares square root is the genuine Euclidean norm, and the p-th power is actual real exponentiation, including the zero norm for p>2. Both weak multiplicative inequalities and all rows are preserved.

4. MinimumSupport is an attained least natural support budget: the all-one weight vector satisfies every exact cost and makes the candidate set nonempty with budget n. Conversely an attained minimum budget equals the minimum actual support, since a smaller support would itself supply a smaller budget. Empty and zero-row inputs cause no undefined minimum.

5. The unrestricted supremum ranges over every finite n,d with d>k and every real matrix, with no input-rank or ambient-dimension cap. ENNReal is essential here: an unbounded set retains supremum infinity until the upper theorem establishes finiteness. Exact natural embeddings and ENNReal.ofReal comparisons preserve the nonnegative bounds without assuming a worst-case matrix attains a real supremum.

6. Part I Section 1 Theorem 1.1 and Part II Section 1 Theorem 1.1 were directly inspected. The even branch minimum has exactly k^(p/2)/epsilon^2 and k^((p+1)/2)/epsilon+k^(p/2-1)/epsilon^2; the non-even branch is k^(p/2)/epsilon^2. The even predicate p=2*s with natural s>=2 exhausts the allowed positive even exponents.

7. The exact lower logarithmic exponent is zero for even powers and 5*p/2+3 otherwise; the common upper exponent is p+5. L=log(2*k/epsilon)>1 on all k>=1 and 0<epsilon<1/2. Positive finite real c<=C are selected after p but before k and epsilon, so no uniformity across p or hidden dimension-dependent constant is added.

8. The literal AdditiveProposal retains Cp*(k^(p/2)/epsilon+k/epsilon^2)*L^cp with positive real Cp,cp, all n,d,k with 1<=k<d, all real matrices and all allowed accuracies. The full universal negation allows bad inputs to depend on attempted constants and applies to each fixed p>2, not just an even example.

9. Part I Section 8 supplies precisely that all-exponent negative answer. Its non-even choice epsilon=k^-1 yields a strict polynomial gap min(1,p/2-1)>0 over the additive proposal; its even choice epsilon=k^-1/4 gives gap 1/4. These exceed any fixed logarithmic factor and are compatible with the target domains for sufficiently large k. This checks the source correspondence, not a new formal proof.

10. All k>=1, all real p>2, every 0<epsilon<1/2, arbitrary input rank and every ambient dimension d>k remain. No efficient construction, signed-weight extension, hyperplane-only test family, even-only regime or fixed input independent of accuracy replaces the full question. The historical partial notices are explicitly retained without overriding the full credited resolution.

## Bound inputs

- docs/lean/statements/RA-05/NUMERICAL_TARGETS.md: 23a9cb637b7b1456fe0a0f06f3ee414c3c7dbcfc5c80a69fc303b7e347166ac5
- docs/lean/statements/RA-05/ORIGINAL.md: 6e03461d0079b656779e5b87d5faa91f198c4c90ea63beb613732226e678181c
- docs/lean/statements/RA-05/source-lock.json: d222ee4017511ce05172f25cc71730c4f810bfabf0145052b75aa98a2db56c06
- randomized-and-low-rank-approximation/RA-05/README.md: 6e03461d0079b656779e5b87d5faa91f198c4c90ea63beb613732226e678181c
- randomized-and-low-rank-approximation/RA-05/problem.tex: dad4fa443e5ce7d94122b9ff1bfcbc8513893471fc456802730170e2ac7ca1b6
- references/holden-further-2026-09-14/RA-05/part-1.tex: 6cc00d4e27c20529eb95a406313bb19fbaee5049bda2febca3d88ec5e3673712
- references/holden-further-2026-09-14/RA-05/part-2.tex: 911fe25ca20da6f3f3b05686d5d646f7aa0604a4488e3b368cdefeff73ef1175

## Limits

Independent AI-agent preimplementation mathematical specification review, independent of author /root. The complete canonical page, specification and relevant explicit theorem/model/negative-answer sections of both archived parts were inspected; all source-lock bytes were verified. This is not a re-audit of every proof in those long manuscripts, a target proof, or approval of any as-yet-unwritten Lean implementation. Final concrete definition/import/pin and kernel/frozen-boundary reviews remain required.
