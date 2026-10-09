# TR-13 specification source-refresh review A

Phase: `specification`.

Reviewer: `/root/refresh_tr13_review_a`, an OpenAI Codex AI agent independent of statement author `/root`. Date: 2026-09-30. Verdict: **approve** for the exact statement-fidelity scope and input bytes bound below.

This is a fresh source re-review after the existing implementation. I did not author the specification, Lean statements, frozen boundary, or source-provenance changes. I have not rerun Lean, a kernel checker, or Linux Comparator. This report does not certify the truth of `Target`, the separate complete-proof project, or the verification claims in the newly added notice.

I compared the complete current canonical README and byte-identical `ORIGINAL.md` against `previous-original.md`. The only canonical change is the 30-line complete-Lean-formalization notice; the retained mathematical Statement, status and credits are unchanged. The notice itself distinguishes its local build claims from pending authoritative Linux and independent final-review gates. I compared the archived and current specifications: only the provenance paragraph preceding `## Exact target` changed; all mathematical specification text from that heading onward is byte-identical.

The original preimplementation specification and source are preserved separately, together with `previous-statement.json` and the unchanged historical reports in the parent directory. I read those historical reports and their recorded chronology. This present review does not pretend to have occurred before implementation or replace that historical evidence with a backdated approval. The refreshed provenance paragraph accurately distinguishes the historical source hash from the current snapshot.

## Independent mathematical assessment

The specification retains all odd orders `m >= 5` and all dimensions `n >= 2` over the complex numbers. The coefficient space has exactly `m*(n-1)+1` entries. The zero-based index sum is equivalent to the original one-based shifted sum. No exceptional tensor, order or dimension is silently discarded beyond the original existential generic-domain restriction.

All five ranks are represented by actual decomposition widths. Ordinary width allows arbitrary products of vectors; symmetric width allows complex scalar multiples of pure powers. The full homogeneous Vandermonde vector `a^(n-1-i)*b^i`, with `(a,b)` not jointly zero, retains both projective endpoints, including infinity. Zero coefficients and vectors allow padding and the zero-width case. An ordinary coefficient may be absorbed into one vector since the target order is positive.

The border definitions allow sequences of arbitrary ambient complex tensors for ordinary border rank and only symmetric decompositions for symmetric border rank. Neither imposes Hankel or Vandermonde structure on the approximants. Every-coordinate usual complex convergence is the source's limit notion.

All-width equivalence is equivalent to equality of the five least ranks here. The width sets are upward closed by padding, including for approximating sequences. Every Hankel tensor has finite Vandermonde width: with `d=m*(n-1)`, `d+1` distinct affine complex nodes span all `d+1` coefficients by the invertible Vandermonde matrix. These decompositions also give finite symmetric and ordinary widths; constant sequences give finite border widths. Thus no arbitrary rank function or existence assumption hides in the threshold formulation.

A polynomial with an explicit nonzero evaluation witness supplies a nonempty principal Zariski-open set. Conversely, for a nonempty affine open whose complement is a common zero set, at a point in the open some defining polynomial is nonzero, giving a principal open contained in it. Existentially choosing such a polynomial for each `m,n`, before quantifying every coefficient vector in its nonvanishing locus, is therefore equivalent to the original nonempty-open existence question. It does not reduce to one witness tensor or assert equality on every Hankel tensor. The known generic numerical rank formula is background, not a separate subquestion in the original displayed equality target.

No specification-fidelity blocker remains. Approval covers correspondence to the retained original target and the clarified source provenance, with the execution and proof limitations stated above.

## Reviewed input hashes

- `docs/lean/statements/TR-13/NUMERICAL_TARGETS.md`: `8238e5adadcc23223017e7900a751f9cd0318b5375886b5543b4b8eb9303d91d`
- `docs/lean/statements/TR-13/ORIGINAL.md`: `fa34e46c5869e28c9f198a1aa78a4a5e026ba99dcbe67ce10d3410e426f7f70b`
- `docs/lean/statements/TR-13/reviews/source-refresh-2026-09-30/README.md`: `abd6d3efd86f6431f3e19590480dc141b0eefec9a5c51952aab4e97aedce8fdd`
- `docs/lean/statements/TR-13/reviews/source-refresh-2026-09-30/previous-original.md`: `da720e9599af7271686127b618b21038685e52a754031c2d43915c9d255f015f`
- `docs/lean/statements/TR-13/reviews/source-refresh-2026-09-30/previous-specification.md`: `1df6ae38c9f787c4d0994c676f149e0fc02ed94b85e5d6e0e65c7e236d744b3d`
- `docs/lean/statements/TR-13/reviews/source-refresh-2026-09-30/previous-statement.json`: `2db388f56748ad553da877334d097ecc01898f11e1523b3da857c03d5d0bdc7c`
- `docs/lean/statements/TR-13/reviews/specification-infra_audit.md`: `bcf09c23139f384ebcb7274f0d745845479b7a433dc62793307b57028fcbeb3d`
- `docs/lean/statements/TR-13/reviews/specification-statement_design.md`: `539fe8aa02e30b71103d5fcf4a929d001d621e0ca50c81b87e6b85412e9a2a79`
- `tensor-computations/TR-13/README.md`: `fa34e46c5869e28c9f198a1aa78a4a5e026ba99dcbe67ce10d3410e426f7f70b`
