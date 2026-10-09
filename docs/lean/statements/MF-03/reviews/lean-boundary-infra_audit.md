# MF-03 independent Lean-boundary review

Reviewer: `/root/infra_audit`, an OpenAI Codex AI agent independent of specification author `/root` and implementation author `/root/statement_design`. Phase: lean-boundary. Verdict: **approve**.

I compared the complete actual live and frozen Lean definitions with the previously approved specification and full canonical README. I inspected pinned polynomial degrees/evaluation, factorial arithmetic, coprimeness, complex norm and finite-sum conventions, and expanded every target helper as described below. Local semantic source hashes are listed below; dependency meanings are additionally identified by their pinned package sources.

NormalizedPadeRepresentation uses actual complex polynomials and exact factorial coefficients. Finset.range (j+1) includes exactly i=0,...,j, so natural j-i is the correct coefficient offset. Every coefficient equation through j=2*m inclusive is required, giving precisely the convolution conditions for Qf-P to vanish to order 2m+1.

I inspected the pinned Nat.factorial recursion, Polynomial.eval and natDegree definitions. Factorials are exact positive natural integers cast to the complex field, with exact reciprocals. Q.eval 0=1 and the j=0 equation imply Q(0)=P(0)=1, so the zero-polynomial natDegree convention cannot change the degree bounds in an admissible pair.

ReducedPadeRepresentation adds the actual Bezout IsCoprime predicate. Over the univariate complex polynomial ring this forbids any common nonconstant factor, and hence common roots. Thus a denominator zero would be a genuine pole; requiring Q.eval z != 0 gives precisely the reduced-rational no-pole condition, not the stronger requirement on arbitrary unreduced denominators.

The explicit existence conjunct is inside the quantifier for every m>=1 and prevents vacuity. Cancellation and normalization preserve the coefficient conditions because all cancelled factors are nonzero at zero; the degree-bound cross-product argument from the approved specification makes all qualifying pairs represent the same rational function.

The complex norm was checked in the pinned API as sqrt(normSq z), namely ordinary complex modulus. Target covers every point of the entire closed radius-three complex disk and requires both denominator nonvanishing and the exact weak norm error bound two. Totalized division at zero cannot bypass the first conjunct. There is no finite-order cutoff, restriction to real z or real coefficients, or stronger strict inequality.

Live and frozen definitions independently compile and their equality elaborates by rfl. Both Target axiom closures contain only propext, Classical.choice and Quot.sound. The target is a closed proposition definition, with no proof body or numerical approximation claiming to settle the original question.

I independently elaborated the live and frozen modules with Lean 4.33.1 into a separate review build directory, then checked the frozen identity by reflexivity. All commands exited 0. Each target axiom report contains only propext, Classical.choice, Quot.sound; #assert_statement and LeanCert #assert_trust kernel both passed. Retained logs are under lean-boundary-infra-audit-evidence/. These are local macOS development checks, not authoritative Linux Comparator execution and not proofs of Target. No numerical domain was reduced and no status promotion is supported by this review.

## Reviewed repository inputs

- `docs/lean/statements/MF-03/NUMERICAL_TARGETS.md`: `7330918bbef9002e38a2d38cd1b019d1170a707e3b8c1e4dfcb18e9b4133dd28`
- `docs/lean/statements/MF-03/ORIGINAL.md`: `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a`
- `lean-statements/NLA/Statements/Infrastructure.lean`: `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37`
- `lean-statements/NLA/Statements/MF03.lean`: `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24`
- `lean-statements/Reviewed/MF03.lean`: `a0c55c3f315c5330d8da170fc2f4c8ac6dab715b8a30b0111660d262ea0d0674`
- `lean-statements/lake-manifest.json`: `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8`
- `lean-statements/lakefile.toml`: `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40`
- `lean-statements/lean-toolchain`: `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71`
- `matrix-functions-and-stability/MF-03/README.md`: `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a`
- `docs/lean/statements/MF-03/IMPLEMENTATION_NOTES.md`: `96171b10dd9fe2a69130a16992e84da8f7b0463373a6ea7a907ba2f18436b859`
- `docs/lean/statements/MF-03/reviews/lean-boundary-infra-audit-evidence/NLA-Statements-MF03.log`: `386f85ffd4e79aadc889dfdd9ec8ec233a64a832de5549d1354c7628b6492409`
- `docs/lean/statements/MF-03/reviews/lean-boundary-infra-audit-evidence/Reviewed-MF03.log`: `6763d920339ce197a8d063f479f5b72cffc8703bb951868aa053d901df1bf1b7`
- `docs/lean/statements/MF-03/reviews/lean-boundary-infra-audit-evidence/identity.log`: `2a3954627795f50423fd88b74045fed1aa6fcc709aa93aa4113bc4d4ac5d9a30`

## Inspected pinned dependency meaning

- mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, `Mathlib/Algebra/Polynomial/Degree/Defs.lean`: `ff616e11c821c0baac9f9f4adb43b28eb1b442ef5e4752a9f8d3469350af7ffc`
- mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, `Mathlib/Algebra/Polynomial/Eval/Defs.lean`: `324a019feeb6134861ed550dcbdff5425ff062b8894024ef852643d5dc873a7b`
- mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, `Mathlib/Data/Nat/Factorial/Basic.lean`: `25fc9752f155b265be6c262e44ac5e92bdff54f1777ca2ea344b76fc4c1fa57f`
- mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, `Mathlib/RingTheory/Coprime/Basic.lean`: `b4209cdf2174b684a50c5b883d99ae5f2963e702f1b8041a1013d3005dd7e809`
- mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, `Mathlib/Analysis/Complex/Norm.lean`: `815efa05d2282b0b234139eac16d614f1128d69e39cf02249df887934ccc9741`
- mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`: `2f39541f66288cb9ae9f77d97fd3656825a1dd1a4b5ca6a156f938d8fa1678a8`
