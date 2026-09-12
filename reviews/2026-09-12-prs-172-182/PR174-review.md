# Independent mathematical and statement-fidelity review — PR #174

**Verdict: PASS, with no mathematical or statement-fidelity blocker found.**

Reviewer: OpenAI Codex AI agent `/root/audit_functions_randomized`, acting as an independent reviewer of the actual sources, not adopting the submitted reviews. Reviewed head: `856b1618b1cad046b3640a13de0df5ef4c10a8f3`, in `/private/tmp/nla-audit-174`. Date: 2026-09-12. This is an AI mathematical/source review, not human peer review or a claim that I locally ran Lean. The integrating agent separately authenticates upstream CI and the default-kernel/Comparator evidence.

## Scope and original-target fidelity

I read the retained canonical TR-15 statement, its version at base `f41f1f9ffa2171550d4bb795862c6170c4f26070`, the informal TR-15 manuscript, and the complete actual `Definitions.lean`, `Proof.lean`, `Challenge.lean`, and `Solution.lean`, together with the Comparator and package configuration. The retained mathematical target is unchanged. Ordinary Git comparison also showed the actual proof/definitions/challenge/exports and package configuration unchanged from the README's immutable proof revision `6a2d0868e8b7905dbd5c04d4beaae8cf43288e1f`.

In `tensor-computations/TR-15/lean/NLA/TR15/Definitions.lean:30–96`, tensors are actual ordered arrays; the Hankel entry is the generating vector at the sum of zero-based indices. The lower tensor has order `m` and dimension `q*(n-1)+1`, and the upper tensor has order `q*m` and dimension `n`, using the same generator. The finite cast in the lower definition only identifies equal generator lengths. Contraction sums all ordered tuples, so multinomial multiplicities are not omitted. `IsHEigenpair` includes a nonzero real vector and all component equations with the signed integer power `x i ^ (s-1)`. `HasNoNegativeHEigenvalues` quantifies over every real eigenvalue and real eigenvector. The universal conjecture retains every odd `m≥3`, all `q≥2`, all `n≥2`, and every generator. No PSD-associated-Hankel-matrix premise, strong-Hankel assumption, or eigenpair-existence assumption has been added.

The primary source, Ding, Qi and Wei, *Inheritance properties and sum-of-squares decomposition of Hankel tensors*, confirms the generator convention, real H-eigenpair definition, and odd-order inheritance question: [author-hosted journal manuscript](https://www.polyu.edu.hk/ama/staff/new/qilq/BIT-DQW.pdf), pp. 2–3 and concluding §4, p. 21. The displayed target is distinct from the stronger associated-matrix-positive-semidefinite setting discussed in that paper.

## Complete proof check

The witness is `m=3`, `q=2`, `n=2`, with generator `(2,0,1,0,2,0,-1)` (`Definitions.lean:99–112`). I independently enumerated the ordered index sums using a short, independently written integer calculation; no contributor code was executed. The resulting lower contractions are

```
C0 = 2*x0^2 + x1^2 + 2*x0*x2 + 2*x2^2,
C1 = 2*x0*x1 + 4*x1*x2,
C2 = x0^2 + 2*x1^2 + 4*x0*x2 - x2^2.
```

These agree with the actual finite-sum expansion in `Proof.lean:28–49`. The first is `(x0+x2)^2+x0^2+x1^2+x2^2`, strictly positive for every nonzero real vector. Thus the first H-eigenpair equation `C0=λ*x0^2` rules out `λ≤0`, including the case `x0=0`, without any division (`Proof.lean:81–108`). This establishes the premise for every lower H-eigenpair, not merely for an exhibited one.

Nonvacuity is separately proved by the intermediate value theorem (`Proof.lean:110–131`). The polynomial `p(t)=2*t^4+2*t^3+3*t^2-4*t-1` has `p(0)=-1` and `p(1)=2`, so a root lies strictly between 0 and 1. The vector `(1,0,t)` is nonzero and satisfies the actual lower equations with `λ=2+2*t+2*t^2`; the third equation is exactly `p(t)=0`.

For the upper order-six tensor and vector `(0,1)`, only the ordered tuple whose five indices are all one survives. The contraction is `(0,-1)` (`Proof.lean:52–79`), agreeing with the fifth coordinate powers times `λ=-1`. The proof establishes nonzero vector, all component equations, and strict negative eigenvalue (`Proof.lean:135–146`). It then proves the full admissible counterexample and negates the complete universal conjecture (`Proof.lean:148–161`). A single admissible counterexample is sufficient for this negative answer; it is not a restriction of the target.

## Exports and trust limits

All seven public `Solution.lean` signatures match the seven `Challenge.lean` targets and are explicit wrappers around the checked proof. Comparator lists all seven and no definition holes. The only `sorry` occurrences in these actual files are the intentionally separate Challenge placeholders; the proof and Solution do not import Challenge. I found no custom axiom, proof hole, native-decision certificate, unsafe evaluator, or custom elaborator in the actual submitted proof chain. The negative scalar sign uses LeanCert's kernel trust setting. The declared permitted axioms are the ordinary `propext`, `Classical.choice`, and `Quot.sound`.

This source review supports the **complete negative answer to the original TR-15 target**, including a nonvacuous lower premise. Promotion to the repository's “Lean verified” status is justified once the integrating agent's independent live-CI/default-kernel/Comparator gate succeeds. I have not substituted the submitted PASS labels for either semantic review or that operational gate.
