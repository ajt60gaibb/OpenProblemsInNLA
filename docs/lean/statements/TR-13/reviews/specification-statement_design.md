# TR-13: independent specification review

Reviewer: /root/statement_design, OpenAI Codex AI agent. Date: 2026-09-28.
Verdict: **approve**, bound to the exact input bytes below.

## Fidelity reasoning

1. The quantifiers preserve every odd order m>=5 and dimension n>=2 and the entire complex Hankel coefficient space of dimension m(n-1)+1. Zero-based sum-of-indices entries exactly match the original one-based shifted formula.

2. All five ranks are retained: ordinary, symmetric, ordinary border, symmetric border and Vandermonde. Ordinary width allows arbitrary products; symmetric width allows complex multiples of arbitrary powers; neither is confined to Hankel factors.

3. The Vandermonde family retains homogeneous pairs (a,b)!=0, including a=0 and b=0 individually and thus the point at infinity. Zero coefficients permit padding even though the projective pairs themselves are nonzero.

4. Ordinary border approximants are arbitrary complex tensors, while symmetric border approximants have symmetric width. Neither sequence is restricted to Hankel tensors. Entrywise usual complex convergence is exactly the specified limiting notion.

5. All-width equivalences characterize equality of the five minimum ranks because the predicates are upward closed under padding and each minimum exists. Ordinary pure products span all tensors. Symmetric pure powers span the symmetric space in characteristic zero. For Hankel tensors, D+1 distinct finite complex nodes give an invertible Vandermonde coefficient system; hence Vandermonde widths are finite as well. Constant sequences supply finite border widths.

6. An explicitly witnessed nonempty principal open D(p) for an actual complex multivariate polynomial is equivalent to existence of a nonempty affine Zariski-open subset with the equalities: any nonempty open is a union of principal opens and contains one through any chosen point.

7. The polynomial and its nonemptiness witness depend on m,n and precede the universal h,r quantifiers. Requiring the equalities only where p(h)!=0 preserves the generic claim without strengthening to every tensor or prescribing a particular open set.

8. The displayed explicit generic rank value in the canonical page is known background, whereas the original question asks equality of the five ranks. Omitting that additional already-known formula from the conjunction does not omit a subquestion or replace the target.

9. The full canonical README and byte-identical ORIGINAL were read, including target, definitions, resolution and preserved historical material. This specification approval is independent of the author /root and precedes implementation.

## Bound inputs

- docs/lean/statements/TR-13/NUMERICAL_TARGETS.md: 1df6ae38c9f787c4d0994c676f149e0fc02ed94b85e5d6e0e65c7e236d744b3d
- docs/lean/statements/TR-13/ORIGINAL.md: da720e9599af7271686127b618b21038685e52a754031c2d43915c9d255f015f
- tensor-computations/TR-13/README.md: da720e9599af7271686127b618b21038685e52a754031c2d43915c9d255f015f

## Limits

Independent mathematical specification review only. Future Lean definitions and the imported TR14 tensor/width constructions require a separate boundary review. No tensor-rank theorem, decomposition algorithm, genericity theorem or original conjecture is proved here.
