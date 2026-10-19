# PF-05 retained candidate: route and exact gaps — 2026-10-18

Independent reviewer: `/root/solved_inventory` (AI agent). Baseline `6e2c960557b6f61af1ed6e679b0634dd498181b2`. The exact mathematical boundary is approved in [PREPROOF_STATEMENT_REVIEW_1.md](PREPROOF_STATEMENT_REVIEW_1.md). **The full Target is still unproved.** This is a proposed finite-dimensional proof route, not proof code or a claim that its missing gates are already discharged. No old worktree/cache was edited.

The candidate's seven actual proof files are under `nonnegative-and-positive-factorizations/PF-05/lean/NLA/Proofs/PF05/`, not a shared proof directory. They total 1,866 lines. Their exact bytes independently replay with kernel trust and only standard axioms; source/type/trust evidence is in [retained-kernel-check/result.json](retained-kernel-check/result.json).

| Existing support file | SHA-256 |
| --- | --- |
| `Basic.lean` | `ed1077fe63c84a5c958b14a4265f68307d67fc67135e2272f2619ec326df77a1` |
| `Congruence.lean` | `2e5899f22fcfe722b03eb73a6ed50e5d4778fdb3f82ca7c464fd1ba36fda7047` |
| `Operator.lean` | `e5e6dd822bb04e2363aabbcf2dea1578b951343208ed072356fdc5f52b923a83` |
| `PositiveReduction.lean` | `e6cbcbb308035d5481cf11855ebac95c5070120bdc81372e2c39e096ebfde31e` |
| `PositiveTopology.lean` | `86b99ca504a8a20ffbc03d01a56f6f2637b5fb07d0a56d7038f1b82ef8b461c3` |
| `ZeroNormalize.lean` | `736d6d03d70ef1de5ed77aa57e1933b5a67435366392e532c10454f936b781b8` |
| `ZeroPair.lean` | `e4a21b1af8026ab97492309a260a44aa0ce8ff2c9a8356d8e3dbdf5022223929` |

The actual reused support is substantial but sharply bounded. Basic proves PSD agreement, the exact 2-by-2 PSD criterion, full-rank coordinate spans and trace separation, and zero factors/directions forced by zero rows/columns. Operator proves an actual invertible 3-by-3 coordinate change between two complete factorizations; it does not represent feasible directions or integrate them. Congruence proves exact preservation of PSD, factorization and feasible directions. ZeroPair/ZeroNormalize prove an actual normalizing congruence for any nonzero orthogonal pair, including both diagonal-coordinate cases. PositiveReduction constructs actual positive-ray compression, preserves rank three and both rigidity/uniqueness predicates, and derives independent outer-product generators for distinct singular rays. It does not prove the positive case. PositiveTopology proves positive-definite aggregate factors and invertibility of a supplied limiting congruence matrix; it proves no compactness, orbit closedness or connectedness statement.

The full dependency map and precise missing obligations are machine-readable in [gap-map.json](gap-map.json). Two branches can proceed independently after the second fresh statement approval.

## Reverse implication for all zero patterns

First prove the actual feasible-direction operator from the first-order trace equations. Reuse Basic's left coordinates X and right coordinates Y, whose off-diagonal weight is two: a coordinate operator T must satisfy E_left=X*T and F_right=-T*Y. The already proved span/left-inverse/right-inverse facts establish existence and uniqueness. This avoids silently substituting the ordinary Euclidean adjoint for the trace adjoint.

Then integrate by X(t)=X*(I+tT), Y(t)=(I+tT)^(-1)*Y. Exact products are automatic; invertibility and primal PSD hold on a sufficiently small common interval. The dual PSD assertion is the genuine missing analytic gate. For each dual factor, split zero / positive definite / nonzero rank one. At rank one, normalize B to diag(lambda,0), lambda>0. If the feasible F has positive bottom diagonal, the actual inverse-path determinant has strictly positive derivative lambda*w at zero, so it is positive for small positive t. If the bottom diagonal vanishes, straight-segment PSD forces the off-diagonal derivative to vanish; F is a scalar multiple of B, and the inverse path is an exact positive scalar multiple of B. Prove a common interval for the finite family. A tangent-cone condition or an unspecified O(t^2) term in the flat case would not suffice.

Under global uniqueness, each integrated exact factorization has a genuine congruence; the original primal factors span, so I+tT itself agrees with that congruence on every symmetric matrix. The rank-one midpoint/line argument on P, Q, P+Q+R and P+Q-R then forces T to be scalar. No differentiable choice of congruence matrices is needed. This yields the full uniqueness=>straight-rigidity direction, independently of positivity.

## Forward implication with a nonzero zero pair

Prove actual removal/restoration of zero rows and columns using finite index embeddings and the already proved forced-zero lemmas. Rank three must be preserved; both properties must be transported for all alternative factorizations and all feasible directions. Positive-ray compression does not remove the zero class and is not a substitute for this gate.

When a zero remains in the nonzero core, normalize its actual pair using ZeroNormalize. Independently normalize the corresponding alternative's pair. Prove the inverse/iff congruence transport, then the shear/reflection reduction of the actual alternative operator to

```text
L(a,b,c) = (a+alpha*b+beta*c, gamma*b, c), gamma>0,
(alpha,beta,gamma) != (0,0,1).
```

Derive the actual inverse-dual formula with the trace pairing's weight two. Construct the submitted source's T(A)=(-sigma*a+alpha*b+beta*c)P, sigma=gamma^2-1, and the exact dual F=d[[sigma,-alpha/2],[-alpha/2,-beta]]. The first-order equations follow directly. Prove PSD straight segments for every rank case. The key boundary check is the exact nonnegative-square identity: if the leading determinant coefficient q is zero, it forces the full direction to be sigma*B, rather than merely a formal nonnegative first derivative. The positive-coefficient case admits an explicit small interval or a proved derivative-sign argument. Spanning proves this induced direction is nonscalar, and finite intersection supplies one common h. No generic zero-pattern or distinct-factor premise is needed.

This route closes the zero-pair forward case without any local-to-global theorem. It still needs the source's actual normal form, explicit direction, interval and nonscalarity proofs; none is contained in the retained seven modules.

## Positive case: close the topology rather than assuming it

The cited [primary article](https://arxiv.org/html/2410.18891v2), Theorem 5.2, states the positive-entry equivalence. Its Lemma 19 invokes connectedness of a factorization quotient. Formalization must explicitly establish the separation and orbit assertions needed for that step. This observation is a proof-obligation analysis, not a claim that the mathematical theorem is false.

The following is this reviewer's concrete proposed closure of the orbit gate. Fix an actual rank-three factorization (A,B), P=sum A_i. PositiveTopology already proves P positive definite. For an actual convergent sequence of congruent factor tuples choose their real invertible S_l. Their row sums Q_l=S_l^T*P*S_l are bounded. Prove a coercive estimate c*||S_l||_F^2 <= trace(Q_l), c>0, from positive definiteness of the fixed P. Consequently S_l is bounded and has a convergent subsequence in the finite-dimensional 2-by-2 matrix space. Continuity gives actual limit row congruences A'_i=S^T*A_i*S. If the limit belongs to the actual rank-three factorization fiber, the candidate's determinant theorem now proves det S !=0. Recover the dual factors either by inverse continuity or, more economically, by Basic's trace separation: the actual limit rows with the standard dual-congruence factors and the given limit columns both produce M, hence the columns agree. This proves relative orbit closedness. The current theorem begins after the subsequence/limit work and cannot be cited as the whole result.

Define the actual fiber of concrete finite factor pairs satisfying Factorization M and its actual congruence relation. The action maps are homeomorphisms. A neighborhood of one point contained in its orbit can be translated to every orbit point, making the entire orbit open. The preceding closedness makes it also closed, or equivalently supplies the required T1 property of the actual quotient. Only then can connectedness force a locally rigid orbit to exhaust the fiber. Connectedness plus an open singleton alone does not do so; a two-point connected non-T1 space already shows the logical failure.

Actual connectedness of this specific quotient remains another major missing theorem. A faithful route is to formalize an actual nested-ellipse/PSD-cone model for the rank-three size-two factorizations and its connected shape parameter space, then prove the model's map to the quotient is surjective and continuous. Supplying an arbitrary connected space or a connectedness premise in the final theorem would be circular. No such model or theorem is in the candidate.

The local rigidity gate is also still missing. PositiveReduction legitimately removes repeated positive rays before using the source's finite cone argument. One route is to prove, for the actual distinct-ray positive instance, that straight (second-order) rigidity implies first-order rigidity modulo the congruence tangent space, then prove local rigidity. Avoid importing a general semialgebraic curve-selection theorem without a Lean proof. A possible elementary replacement is a proved local GL(2) gauge via the finite-dimensional implicit-function theorem, followed by normalization of hypothetical nearby noncongruent operators and a compactness limit yielding a nontrivial first-order direction in the complementary slice. The derivative of the congruence action must be computed and a real local slice proved; invoking the words 'local slice' is not a proof. The finite cone implication, slice and actual quotient connectedness are explicitly open implementation gates, not established by this review.

The positive route is consequently likely the largest remaining part of PF-05. Keep those contracts explicit during development. Do not export Target while any local-to-global, connectedness, cone or slice gate is merely assumed. The final canonical proof must retain repeated factors via the proved compression transfer and restore the original p/q indices and all zero rows/columns.

## Final assembly, evidence and preservation

Assemble the unrestricted reverse implication with the two forward cases after actual zero deletion: either the retained core is strictly positive, or it contains a nonzero zero pair. Restore the original fixed factors and export only the unchanged full Target. A rank-three size-two factorization cannot have PSD rank one (its size-one trace product would have ordinary rank at most one); prove this small transfer if the positive core API needs the original PSDRankTwo predicate.

Before any acceptance claim, exact-copy the reviewed proof closure into the canonical package, retain the original statement and its frozen identity, replace the stale manifest-copy receipt truthfully, run fresh independent complete source/kernel audits and the actual isolated Linux Comparator harness. Keep canonical status Solved and whole_problem_verified false until that evidence is accepted. No registry or canonical mathematical target change is required.

Reproduce the retained support replay from this directory:

```bash
python3 check_candidate_kernel.py --evidence-name retained-kernel-check
```

The driver reads frozen snapshot sources and clean pinned external objects, creates fresh temporary NLA objects and retains all commands/log hashes. It never writes the old candidate or its dependency cache. Its historical consumer filename is `IndependentTreeColorAudit.lean`; its retained body audits only PF-05 declarations. A successful support replay is not a proof of the full Target.

Input inventory SHA-256: `7fddbe64261ae153702d9cadd22f011502a5bd01dfffd6243ae9349f95254d28`.
Gap map SHA-256: `2105c56cdabd54d456a6bd3c7f325a93b01f1d04deb7ea6822098cf50f2f0b93`.
