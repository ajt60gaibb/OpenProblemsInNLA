# MI-06 independent statement referee 2 — PASS

Date: 12 September 2026. Reviewer: OpenAI Codex agent `/root`, independent of the statement implementer `/root/formal_review_standards`. **Verdict: approve the frozen six-export statement boundary for proof implementation once referee 1 also approves. No statement correction is requested.** This is statement review, not proof completion, Linux verification or external human peer review.

I read the complete canonical page, Colbrook's complete source TeX, every Definition and Challenge declaration and the numerical plan. The canonical page and both source files are byte-identical to upstream `587bd896f0e1006f4a4b7f38555e3a523ef85176`. I independently compiled Definitions and Challenge into a fresh artifact prefix, then inspected fully elaborated definitions and all six signatures against those fresh artifacts. All three commands exited zero; only the six deliberate Challenge placeholders produced warnings. No Proof or Solution implementation existed during these checks, and every reviewed source hash remained unchanged. All ten actual dependency HEADs match the pinned manifest with clean tracked source.

## Original target and genuine objects

`DominationConjecture` retains every positive dimension, every pair of arbitrary complex square matrices, and existence of two arbitrary complex unitaries. It is precisely the original ordinary PSD inequality with factor `Real.sqrt 2`, embedded into the complex scalars. No positivity, Hermitian, real, invertibility, rank or commutation assumption narrows those arbitrary inputs. The factor is the nonnegative real square root, not an unconstrained scalar or approximate literal.

I inspected the pinned definition of `CFC.abs`: it is the actual positive CFC square root of `star X * X`. Matrix star is conjugate transpose. `symmetricModulus` is the actual arithmetic average of the right and left moduli. I also inspected `Matrix.le_iff`, which identifies the elaborated matrix order with positive semidefiniteness of right minus left, and the actual unitary-group definition and star-inverse identities. This is neither entrywise order nor a norm inequality. The first public export requires the genuine square-root identity and positivity for every complex X.

The final `¬ DominationConjecture` is a complete negative answer to the retained canonical question. The fixed rational dimension-three witness suffices for that universal negation. The source's stronger no-finite-constant theorem is excluded and must not be claimed by later publication of this certificate.

## Exact witness, tables and homogeneous obstruction

The witness is exactly Colbrook's rational specialization t=3/4. My independent Fraction calculation checks all six candidate-modulus squares against their correct ordered Gram matrices. The two nondiagonal roots are positive multiples of the outer products of (4,3,0) and (4,0,3); the other four root occurrences are positive diagonal matrices. Thus the numerical root candidates are sound. Their equality to the actual CFC moduli remains a required Lean conclusion, to follow from proved positivity and square-root uniqueness.

The same independent calculation checks both displayed symmetric matrices, the actual sum candidate diag(3/4,3/8,3/8), and both rank-one decompositions. In particular, the missing directions are the projectors at Lean coordinates 2 and 1, respectively; there is no one-based/zero-based indexing error. The two coefficient-one-eighth identity terms, one-tenth outer products of (3,1,0) and (3,0,1), and subtracted missing projectors reproduce all entries exactly.

`squaredLength` is the explicit sum of `Complex.normSq` of the coordinates, and `quadraticForm` is the real part of the genuine conjugate-vector matrix quadratic form. Fresh elaboration retains the pointwise complex conjugation and actual matrix-vector product. `rankOne w` is the actual outer product `w w*`. No default function sup norm or substituted PSD predicate appears.

For any two complex vectors a,b in dimension three, the linear map w ↦ (a*w,b*w), with conjugate transpose understood in each scalar product, has codomain dimension two and therefore a nonzero kernel vector. The required positive squared length makes this a genuinely nonzero vector even when a,b are dependent or zero. The statement imposes no independence hypothesis. This universal linear-algebra obligation must be proved, not replaced by a search over selected unitary matrices.

For arbitrary complex unitaries U,V, choose that vector orthogonal to Uu and Vv. The rank-one terms vanish in its quadratic forms, the two subtracted conjugated projectors are nonnegative, and the identity terms yield the two upper bounds of one eighth times its squared length. The diagonal sum gives the lower bound of three eighths. These three bounds are required conclusions using the **actual** CFC expressions, not assumptions about numerical tables. Using a positive-length vector instead of a unit vector is the homogeneous version of the source argument; normalization and its extra square root are unnecessary.

Taking real parts is legitimate for this obstruction because genuine complex PSD nonnegativity implies nonnegative real quadratic form. The eventual proof must explicitly use that implication and the relevant conjugation identities. It cannot substitute real-part nonnegativity as a different definition of the conjectured order.

## Minimal numerical certificate and remaining gates

The exact scalar check is 2<9/4, with rational gap 1/4. Together with nonnegativity of the actual real square root, this gives sqrt(2)<3/2 and hence sqrt(2)/4<3/8. Positive squared length turns the three quadratic bounds into a contradiction for **every** unitary pair. The scalar LeanCert certificate must remain in the proof of that contradiction in explicit kernel mode. No unitary search, approximate eigenvalues, matrix-root intervals or interval subdivision is needed.

I applied the relevant Tau Ceti correctness/faithfulness, scope, computation, reuse and attribution standards to this frozen NLA boundary. Mathematical proof attribution remains Matthew J. Colbrook. Formalization credit is George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI assistance and no George email or claimed human endorsement.

After both statement approvals, two independent final proof referees must review the completed analytic bridges and six exports. Actual Linux Comparator must then check the frozen statement correspondence, no replaceable definition holes, default-kernel replay and the permitted transitive axiom set `{propext, Classical.choice, Quot.sound}`. The six Challenge placeholders remain confined to this template, which Solution must never import. No canonical status has been changed by this review.

Fresh commands, raw logs, elaborated inspection, exact numerical reconstruction and source/package identities are retained in [statement-referee-2-root-evidence](statement-referee-2-root-evidence/). The inspection log SHA256 is `48cebba5e680bd88f15a29756ada4bcb6bd067afb2c391143b521d90d28fcc6b`.

| Frozen file | SHA256 |
| --- | --- |
| `NLA/MI06/Definitions.lean` | `a89c6604d36aec8ae3428df7663a2dbb6f2f923b13ca5f7746aaf4f424cb29d2` |
| `Challenge.lean` | `7774d76c9e362c0f808ee4c1fec3b5607359048d5af82d0e99f60b74c52326dc` |
| `NUMERICAL_TARGETS.md` | `792aa98aa94d18d7b49e4e4b66edca89881f1e38cf51c3aacfed8525644509a4` |

Any substantive statement change reopens the affected independent reviews before implementation.
