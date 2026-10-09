# TR-13 independent preimplementation specification review

Reviewer: `/root/infra_audit`, an OpenAI Codex AI agent independent of the target specification author. Phase: specification. Verdict: **approve**.

I read the complete canonical README and exact specification and independently checked the proposed mathematical representation before any target Lean implementation. Infrastructure authorship does not make this reviewer an author of these problem specifications.

The quantifiers retain every odd natural m>=5 and every n>=2. The target asks for existence of a nonempty open domain in the full complex Hankel coefficient space and all five rank equalities there; it is not changed to the separate all-Hankel rank question TR14 or to a sampled finite range.

The reviewed TR14 zero-based Hankel coordinate and ordinary/symmetric width definitions preserve exactly the source tensor entries. Width r means rank at most r because zero terms permit padding, including r=0 for the zero tensor. Over complex numbers these finite minima exist.

Vandermonde width uses the complete homogeneous vector a^(n-1-i)*b^i with (a,b) not both zero. It retains a=0, the projective point at infinity, as well as b=0. Zero coefficients allow padding; no distinct-node, nonzero-weight, affine-only, real or positivity restriction is imposed.

The ordinary border predicate permits arbitrary complex tensor approximants at every sequence index; the symmetric border predicate requires only actual symmetric decompositions, not Hankel or Vandermonde approximants. Full coordinate convergence is exactly the canonical entrywise complex convergence, and neither border definition is replaced by a restricted structured limit.

Each of the five width predicates is upward closed, and every Hankel tensor has finite admissible width (for example D+1 distinct affine Vandermonde nodes span the D+1 coefficient entries); constant sequences give finite border widths. Equality of the predicates at every natural threshold is therefore equivalent to equality of all five least widths, as specified.

A polynomial with an explicit coefficient-vector witness p(h0)!=0 defines a nonempty principal Zariski open D(p). Conversely, if a nonempty affine open has complement V(S), at any point of the open some polynomial in S is nonzero and its principal open is contained in the original open. Requiring the rank property on some D(p) is thus equivalent to the original nonempty-open existence, with no invented genericity oracle.

The extra generic Vandermonde-rank value stated as background is not substituted for or conflated with the five-rank equality question. Complete ORIGINAL.md bytes match the canonical README; all endpoint, parity and dimension guards remain exact.

This approval applies only to the input bytes below. It verifies statement fidelity, not truth of the conjecture or cited resolution, human peer review, a Lean boundary, or Linux Comparator execution. The implemented definitions still require independent boundary review.

- `tensor-computations/TR-13/README.md`: `da720e9599af7271686127b618b21038685e52a754031c2d43915c9d255f015f`
- `docs/lean/statements/TR-13/NUMERICAL_TARGETS.md`: `1df6ae38c9f787c4d0994c676f149e0fc02ed94b85e5d6e0e65c7e236d744b3d`
- `docs/lean/statements/TR-13/ORIGINAL.md`: `da720e9599af7271686127b618b21038685e52a754031c2d43915c9d255f015f`
