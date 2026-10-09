# NM-03: exact nonnegative rank-two approximation complexity

Preimplementation specification by OpenAI Codex AI agent `/root`, 2026-09-28. Two independent approvals must precede code. Complete canonical README is retained byte for byte as ORIGINAL.md; source-lock.json binds it, problem.tex and the retained Colbrook manuscript. No original ID, path, mathematical target, status or credit is changed.

## Complete decision problem

Input data are arbitrary rational m-by-n X with every X_ij>=0 and rational tau>=0. For every such input the exact yes predicate is

exists W:Matrix(Fin m)(Fin 2)Real, exists H:Matrix(Fin 2)(Fin n)Real,
  every W_ik>=0 and every H_kj>=0 and
  sum_i sum_j ((X_ij:Real)-sum_{k:Fin 2} W_ik*H_kj)^2 <= (tau:Real).

All factors are real, with arbitrary precision and no rational-witness assumption. Inner dimension is at most two because the two available factors may have zero columns/rows. There is no exact-rank-two promise on X, no symmetry/positive-definiteness/spectral restriction, and no positivity requirement on factor entries. Zero entries, zero threshold, rank-zero/rank-one outputs and equality at the threshold remain allowed. The norm is the complete squared Frobenius sum, not the operator norm or unsquared error.

Use natural m,n in the input data. All positive rectangular sizes are included. The canonical statement supplies no lower-dimensional edge-case exclusion; allowing m=0 or n=0 as well gives the usual empty matrix whose displayed sum is zero. Those trivial inputs are accepted when tau>=0 and impose no change on the complexity classification. The final notes must disclose this explicit empty-format convention rather than silently assuming invertibility or a minimum size.

## Actual binary encoding and language

A concrete Input structure contains m,n, the full rational matrix and rational threshold. Its binary word is

encodeNat(m) ++ encodeNat(n) ++
  concat_{i in increasing Fin m, j in increasing Fin n} encodeRat(X_ij) ++
  encodeRat(tau).

Use the already reviewed canonical length-framed natural and reduced signed-numerator/positive-denominator rational encoders in NLA.Computation.BinaryEncoding. The matrix entries are in dense row-major order; dimensions and every numerator/denominator bit count. The two dimension fields determine the exact number of coefficients. The encoder is explicit; no arbitrary input-size function or rational unit-cost convention is supplied. A helper may be defined in the NM03 module without changing the previously reviewed shared model. General codec inverses and polynomial translation proofs remain later proof obligations; the actual grammar must be inspected now.

ValidInput means the stated nonnegative entries and threshold. Define the ordinary binary language

DecisionLanguage = { word | exists a:Input,
  word=Encode(a) and ValidInput(a) and MathematicalYes(a) }.

Words which do not encode a valid mathematical instance are negative by the ordinary language convention. There is no separate analytic promise or promise-recognition task. Both the classification and the optional P question refer to precisely this same fixed language. A reduction may not change the interpretation of its output words.

## Complete classification proposition

The original asks for a complexity classification and explicitly offers P membership and polynomial many-one NP-hardness as possibilities without claiming they exhaust every possible classification. Its retained resolution establishes NP-hardness. State

Target := Complexity.ManyOneNPHard DecisionLanguage.

Expanded using the reviewed concrete model, this means: for every binary language L with a finite polynomial-time verifier and uniformly polynomial-length binary certificates, there is one finite deterministic Turing transducer M and one fixed polynomial bound p such that for every source word w there is an actual output v produced by a terminating run of M in at most p(length(w)) machine steps and

w in L iff v in DecisionLanguage.

The finite alphabet/control table, actual tape-step semantics, terminal output and bound are the existing reviewed NLA.Computation.FiniteMachine and Complexity definitions. Machine and runtime constants precede all input words. Reduction computation is ordinary binary bit computation, with no oracle queries, unit-cost rational arithmetic, free reduction function or assumed cost callback. The NP verifier quantifies actual binary certificates and bounded executions; no numerical equivalence alone can stand in for NP-hardness.

Optionally export `PolynomialSolvability := Complexity.InP DecisionLanguage` as the original P alternative, with the same closed-statement checks, while keeping Target the credited NP-hardness answer. Do not assert its negation: NP-hardness does not imply P!=NP. No NP-membership, NP-completeness, constant-factor approximation hardness, strong NP-hardness or exclusivity of the two alternatives is part of the original target.

## Source and numerical correspondence

The retained manuscript Section 1/Theorem 1 reproduces the exact unrestricted decision predicate and proves the NP-hardness alternative, even for positive symmetric positive-definite square inputs. Sections 2–4 construct a rational reduction from positive one-in-three satisfiability. For the Boolean equation matrix C and rational orthogonal row projector P, the construction has N variables including two anchors,

delta=1/(12N), epsilon=1/(24N^2),
X=I+(delta/N)*1*1 transpose-epsilon*P,
tau=N-rank(C)-2+rank(C)*(1-epsilon)^2.

These are supporting proof constants, not additional restrictions on Target or an implemented reduction. The later inverse-polynomial error gap and simple-spectrum rational perturbation strengthen the construction; neither is required to state this exact threshold classification. Real factor feasibility, equality at tau, and ordinary squared-error computation remain mandatory throughout. Existing proof and source credit remain as preserved in ORIGINAL.md; no new proof, human peer review or novelty assertion is made here.

## Implementation and review boundary

The mathematical predicate, dimensions, encoder and fixed language must be fully concrete. A safe closed Target uses the shared pinned Lean/Mathlib/LeanCert dependencies, explicit kernel trust, #assert_statement and #assert_trust kernel, and a separately frozen copy. Review all real/rational coercions, Fin 2 factors, nonnegative guards, squared-error sum, exact encoder and full NP/finite-machine import closure. A frozen identity certificate proves correspondence to the reviewed proposition, not NP-hardness. No reduction implementation, satisfiability proof, exhaustive finite matrix sampling or interval computation is required merely to define the complete original classification answer. All such theorem obligations remain separate.
