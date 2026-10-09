# PF-05 independent Lean boundary review

Reviewer: OpenAI Codex AI agent `/root/inventory`, independent of the statement authors (/root and /root/infra_audit).

Phase: `lean-boundary`. Verdict: **APPROVE** the exact statement boundary. No target proof is asserted.

The complete canonical README and ORIGINAL snapshot agree byte for byte, and the implementation matches the separately approved specification. All actual local definitions were read; the source and frozen module are identical except for the required namespace substitution and frozen comment. Every local import and dependency-pin file is bound below.

Factorization uses actual matrix multiplication and Matrix.trace, real symmetry and a nonnegative quadratic form for every real vector. PSDRankTwo is existence at2 and absence at1, exactly the positive-size minimum. Target explicitly retains entrywise nonnegativity, Matrix.rank=3 and all fixed size-two factorizations.

FeasibleDirection retains symmetry of E,F, the first-order trace derivative and one h>0 shared across every row and column for every real 0<=t<h. The quantified perturbed matrices must actually be PSD. It adds no requirement that their products continue representing M at positive t.

InfinitesimallyRigid uses one shared scalar d with the positive and negative factor signs in the original positions. UniqueUpToCongruence quantifies every alternative factorization then one shared S with det S!=0 and precisely S.transpose*A*S and inverse(S)*B*transpose(inverse(S)). The guard makes Mathlib nonsingular inverse a genuine inverse. The equivalence is present in both directions and includes zeros, singular/repeated factors and zero-trace entries without extra hypotheses.

The declaration is an actual closed safe Prop definition and retains the kernel-trust and transitive-axiom assertions. The inspected author-local elaboration output reports only propext, Classical.choice and Quot.sound. Recorded source hashes match the reviewed bytes. Compilation evidence was inspected, not independently rerun in this review; the frozen equality is not a proof of Target.

## Scope limits

Mathematical/source review and checked author-local elaboration evidence only. This is not external human review, a newly proved solution, or an independently executed Linux Comparator run. Numerical computation is unnecessary to state this symbolic target.

## Reviewed input hashes

- `docs/lean/statements/PF-05/NUMERICAL_TARGETS.md`: `d5c00daa8a0bfa9b520c999b017217ab07fe9bb76b2cac6240f12f241b5db184`
- `docs/lean/statements/PF-05/ORIGINAL.md`: `f7acc0629067696f7aa2828673740e286730fb9654348b742752eb146a840f71`
- `lean-statements/NLA/Statements/Infrastructure.lean`: `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37`
- `lean-statements/NLA/Statements/PF05.lean`: `3ac9a2fb395d96c3b61c6f2593144caac010da4bfafd2d96f86627aa7a75859d`
- `lean-statements/Reviewed/PF05.lean`: `df79daee68563e5bb6a6d85cf70246bf2154f12bcc5fe5a6a806e8009e558b7f`
- `lean-statements/lake-manifest.json`: `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8`
- `lean-statements/lakefile.toml`: `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40`
- `lean-statements/lean-toolchain`: `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71`
- `nonnegative-and-positive-factorizations/PF-05/README.md`: `f7acc0629067696f7aa2828673740e286730fb9654348b742752eb146a840f71`
