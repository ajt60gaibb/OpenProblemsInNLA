# Proposition 3.2 verification

Lean 4.33.1 (`819816b2e0a3bf405af45ae5cc7af2491d8f5bee6`), WSL Ubuntu x86_64.
Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.

The manifest records 100 checked modules. Each was checked with
`lake env lean -o .lake/build/lib/lean/<module>.olean <module>.lean`
in dependency order. This update checked all five new modules and rechecked the
`LikelihoodComparison` import boundary, without warnings. The 95 earlier
component checks are retained; their source hashes are unchanged except for
the import boundary. The original `RadialTail` and `SourceMarginals`
dependencies were checked separately; `SourceMarginals` retains its existing
linter suggestions. No `lake build` was run.

`lake env lean verification/proposition32/Inspect.lean` produced `check.log`.
All 808 audited declarations use only `propext`, `Classical.choice`, and
`Quot.sound`.

The audit includes `proposition_3_2`, `source_second_moment_comparisons`,
`lemma_3_3`, `lemma_3_4`, `lemma_3_5`, the exact Gaussian density bridge,
the original row-kernel identities, the planted cone decomposition, the
reference determinant formula, mixed-kernel Cauchy–Schwarz, and the uniform
Taylor remainder. It also covers the normalized-Gaussian Haar column, Gamma/simplex
change of variables, spherical projection density, sequential Haar law, and exact
overlap density and support. The final audit includes the matrix Lebesgue/Gaussian
coordinate bridge, local/tail majorant, its integrability and rescaling, and the
completed likelihood comparison. No analytic estimate is assumed.

These checks cover the full Proposition 3.2 and its prerequisites. The separate
`Solution` import closure and the full FR-05 theorem were not verified here. See
[the proof description](../../PROPOSITION_3_2.md) for the statement and scope.
