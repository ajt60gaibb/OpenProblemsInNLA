# Independent full-source review: TR-04

Date: 2026-09-11. Verdict: **PASS for the entire exact canonical target.** Recommended status: **Solved, affirmative**, expressly for strict pointwise squared-error improvement in the idealized arithmetic/SVD model. The manuscript does not establish a uniform smaller approximation constant. No mathematical source correction is required.

This is independent Codex-agent mathematical review, not external human peer review or formal verification. I did not change the manuscript, diagnostic source or canonical entry. Duplicate submissions TR-06, TR-15 and TR-26 were excluded from this task.

## Complete sources and identity

I read the complete manuscript `.cache/tensor-recovered/tensor_recovered/manuscripts/TR-04/main.tex`, including all six sections, both lemmas, the theorem, the sharp limiting example, scope statements and bibliography. I separately inspected all of `.cache/tensor-recovered/tensor_recovered/code/verify_tr04.py` before execution and compared the current complete canonical `tensor-computations/TR-04/README.md`.

SHA256 values below are computed on the complete UTF-8 contents after replacing CRLF with LF, without trimming or any other normalization:

| File | SHA256 |
| --- | --- |
| `manuscripts/TR-04/main.tex` | `92672973cdd3efebd43ad4d898c8a8387360a592d6fa3dce27acffba74b61867` |
| `code/verify_tr04.py` | `18ef2b33705ca9e69e7a27e90a4f47cbd3b44e300080af1c3a932cf65c615abb` |
| Independent output `.cache/tensor-recovered/reviews/TR-04-rerun.json` | `eff0602876b8da933d6f3a733cdc542d14b4c675cbcf9ed3c4e5d89be9e9fb6b` |

Manuscript locators: target §1 at line 33; completion Lemma 1 at line 58; finite algorithm §3 at line 97; matrix equality Lemma 2 at line 140; main Theorem 3 at line 167; limiting family §5 at line 210; reproducibility and scope §6 at line 245. The theorem numbering is shared between lemmas and theorems.

## Exact target and primary-source checks

The canonical asks for a single polynomial-time algorithm, valid for every real dense input, every order d>=3, all mode sizes at least two, and arbitrary positive rank bounds. Its output must obey all prescribed unfolding rank caps. For positive optimal squared error E*, it requires squared error strictly less than (d-1)E*. At zero optimum it requires exact reconstruction. Its computational model explicitly permits idealized exact arithmetic/SVD. These are precisely the manuscript's conditions and conclusion.

Primary sources accessed on 2026-09-11:

- [Amsel et al., workshop report v3, §6.1, Problem 6.1](https://arxiv.org/html/2602.05394v3#S6.SS1), dated 21 August 2026, displays a strict inequality for tree networks and expressly allows any such strict improvement while describing stronger asymptotic improvements as desirable. The canonical is its tensor-train specialization, with the necessary zero-optimum qualification. Thus the pointwise/uniform distinction is not an invented replacement target. This review does not settle arbitrary tree networks or the stronger bounds mentioned there.
- [Oseledets, Tensor-Train Decomposition, published article](https://users.math.msu.edu/users/iwenmark/Teaching/CMSE890/TENSOR_oseledets2011.pdf), Theorem 2.2 on printed page 2299 and Corollary 2.4 on page 2300, gives the squared sum of unfolding-tail errors and the usual quasioptimality bound, as well as existence of a best bounded-rank approximation. The paper's induction handles the combined first two indices used here. [Publisher DOI](https://doi.org/10.1137/090752286). The DOI fetch failed in this session; the university-hosted copy of the actual published article was read instead.

The manuscript contains enough linear-algebra detail to check its additional argument independently; it is not relying on a new external conjecture. No priority claim is inferred from these checks.

## Independent proof audit

### Existence and completion estimate: PASS

The feasible set is the intersection of finitely many closed determinantal sets and contains zero. A minimizing sequence can be restricted to a bounded ball, so a best Y exists. This avoids the nonexistence phenomenon for a different tensor rank notion.

For an orthonormal first-mode factor U with k<=r1, compression has dimensions k by n2 by ... by nd. Combining the first two indices gives an order-(d-1) tensor, with exactly d-2 remaining cuts. At any remaining cut, compressing a feasible Y multiplies its unfolding on the left by U^T tensored with an identity; rank cannot increase. Lifting a completion reverses this transformation without increasing any cut rank and imposes first-cut rank at most k.

Apply the usual TT-SVD bound to this compressed feasible comparator. Its squared error is at most (d-2)||U^T(A-Y)||_F^2. The lifted completion error lies in the range of the first-mode projector P, orthogonal to (I-P)A. Pythagoras therefore gives exactly

`error(X_U) <= ||(I-P)A||_F^2 + (d-2)||P(A-Y)||_F^2`.

There is no erroneous use of the original E* in place of the smaller projected residual at this step. That distinction is essential to the later equality analysis. The base case d=3 is simply one matrix SVD after compression and is included. An empty first column space occurs only at A=0, which the algorithm handles separately.

### Matrix equality characterization: PASS

Suppose the best feasible Y attains the first unfolding's rank-r1 lower bound epsilon^2>0. Write S=col(Y_(1)), with dim S<=r1. Orthogonal projection gives two nonnegative errors. The discarded projection error is itself at least epsilon^2, so equality forces Y_(1)=P_S A_(1), and S maximizes captured energy.

There are more than r1 positive singular values in this case. Consequently an energy-maximizing S has dimension exactly r1. In an eigenbasis of A_(1)A_(1)^T, a rank-r1 projector has diagonal weights between zero and one, with sum r1. Maximizing the weighted eigenvalue sum forces weights one above the boundary tau^2 and zero below it. For an orthogonal projector, diagonal weight one means the associated vector lies in its range; weight zero means it is orthogonal to the range. Hence S=H direct-sum E0 with dim E0=s in the tau eigenspace E. In particular P_H(A-Y)=0, and if s=t, P_E(A-Y)=0 too. The argument covers every optimizer and every boundary multiplicity; it does not assume a particular SVD of Y or a unique best approximation.

### Finite candidates and strict inequality: PASS

Every candidate projector keeps all singular directions above tau and exactly s directions in its tau eigenspace, so all discard exactly epsilon^2. If epsilon^2<E*, the completion estimate immediately gives error <= epsilon^2+(d-2)E* < (d-1)E*. This includes rank(A_(1))<=r1 whenever E*>0.

For epsilon^2=E*>0 and s=t, the sole candidate annihilates the optimal residual. Its error is at most E*, strictly below (d-1)E* because d>=3.

For 0<s<t, in any orthonormal basis of E, each coordinate belongs to exactly s of the t cyclic windows. Thus sum_j P_Wj=s P_E. Using P_H R=0 and projector orthogonality,

`(1/t) sum_j ||P_j R||_F^2 = (s/t)||P_E R||_F^2 <= (s/t)E* < E*`.

Therefore at least one completion has error at most `[1+(d-2)s/t]E*`, which is strictly below the requested factor. The returned candidate minimizes actual computable error, so it inherits this guarantee without knowing the favorable index, E* or Y. No search over the infinitely many subspaces of E is needed, and no aligned basis for E0 is assumed.

If E*=0, A is feasible. The chosen projector contains its entire first column space and compression preserves feasibility at the other cuts. Each exact SVD truncation discards zero, or equivalently the completion estimate with Y=A is zero. Thus the algorithm returns A exactly. All signs and both strict-inequality case splits are correct.

### Determinism and polynomial cost: PASS in the stated model

There are at most t<=n1 candidates. Each requires d-2 ordinary SVD steps on arrays bounded polynomially by the original dense array size, followed by lifting and a Frobenius norm computation. Rank caps can always be truncated to unfolding dimensions; oversized supplied caps do not cause oversized allocations in the mathematical construction. The number and sizes of exact arithmetic/SVD operations are polynomial in the dense input size and rank parameters.

Any fixed deterministic SVD/basis convention suffices, since the proof holds for every tie basis and every completion tie choice. If a model requires an explicit convention for a repeated left singular subspace, its projector can be obtained from the SVD and a basis selected by scanning projected coordinate vectors and orthonormalizing the independent ones; this uses polynomially many exact operations. Thus the phrase “any fixed orthonormal basis” does not hide nondeterministic advice. Comparisons of singular values, zero tests and final error comparisons are exact model operations here.

There is no bit-complexity or tolerance guarantee: the strict gap can approach zero, and a near tie is not an exact tie. The canonical explicitly fixes the permitted idealized model, so this limitation does not leave a canonical case unsolved.

### Fixed-format limiting family: PASS

For ranks (2,1), the last cut rank one forces a feasible nonzero tensor to have form M tensor v, where v can be normalized and rank M<=2. At v=(c,s), contraction of the example yields diag(alpha c,beta c,gamma s). Maximizing the retained energy is the maximum over three pairs of singular directions, and then over c^2+s^2=1. The pair energies give maxima alpha^2+beta^2, max(alpha^2,gamma^2), and max(beta^2,gamma^2). Under alpha>gamma>=beta>0 their overall maximum is alpha^2+beta^2. The total energy minus this value is gamma^2, proving the exact optimum.

If gamma>beta, the first chosen subspace is uniquely span(e1,e3); at the remaining cut alpha>gamma forces retention of the alpha term. Error is beta^2+gamma^2. With alpha=2, beta=1 and gamma approaching 1 from above while remaining below 2, the ratio approaches 2. At the endpoint an ordinary tie choice can give equality two, whereas the finite tested candidates avoid equality. Thus even in this fixed format the proposed algorithm has supremum ratio two. This does not establish an obstruction to a different algorithm attaining a uniform smaller constant.

## Diagnostic inspection and fresh execution

The inspected script performs local NumPy/SymPy calculations, creates the specified output directory and writes one JSON report. It does not download, send, delete or publish data. I ran it with `--output .cache/tensor-recovered/reviews/TR-04-rerun.json`, preserving the supplied evidence. Existing Python and cached dependencies were used; no packages or permissions were changed. Initial sandbox runs could not load the existing SymPy installation correctly; a permitted run with access to that installation completed with exit code zero.

Fresh result: **PASS**, NumPy 2.3.5 and SymPy 1.14.0. It covers 91 exact averaging cases (2<=t<=14), three exact rotated tie examples, six rational members of the approaching-two family, 40 random tensors across five formats, five feasible reconstruction cases, the zero tensor, and four numerical rotations of the tied example. Maximum recorded relative reconstruction error was approximately 1.142e-15.

The exact rotated-example implementation zeroes the second last-mode slice only after projection. This is appropriate: the two projected last-mode columns remain orthogonal, and the first has norm at least two while the other has norm at most one, so the second SVD retains the first. The random diagnostic compares with a maximum-cut lower bound, not a numerical global optimum. Its assertions are valid supporting checks for those samples. Numerical rank and tie tolerances make the implemented routine illustrative; it is not a certified realization of the universal exact guarantee. The finite averaging checks do not prove the all-t identity, which was checked directly above by counting appearances.

## Status recommendation and remaining scope

**Recommend Solved for TR-04.** The complete proof establishes one deterministic polynomial-time arithmetic/SVD algorithm with strict pointwise error below (d-1)E* for every positive-optimum canonical input, exact reconstruction at zero optimum, and unchanged rank bounds. No canonical cases remain under that model.

Any resolution notice should retain “strict pointwise” and the arithmetic/SVD qualification. It must not claim a uniform worst-case constant smaller than d-1, a finite-precision/bit-complexity guarantee, a practical stability margin, or resolution of every tree-network variant in the source workshop question. The original target and permanent ID should remain unchanged.
