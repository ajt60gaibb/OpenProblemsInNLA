# TR-13 exact mathematical and numerical specification

Author: OpenAI Codex AI agent `/root`, 2026-09-28. Preimplementation specification; independent approval is required before Lean implementation.

Permanent ID `TR-13`; canonical path `tensor-computations/TR-13/README.md`; campaign base `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`. The complete canonical README is preserved byte-for-byte in `ORIGINAL.md` (SHA-256 `da720e9599af7271686127b618b21038685e52a754031c2d43915c9d255f015f`). Canonical status, author credit and original mathematical target are unchanged.

## Exact target

For every odd natural order m>=5 and dimension n>=2, there exists a nonempty Zariski-open subset of the full complex Hankel coefficient space C^(m(n-1)+1) on which ordinary rank, symmetric rank, ordinary border rank, symmetric border rank and Vandermonde rank are all equal. This is the original rank-equality question, without replacing it by equality only of some ranks or by the separate all-Hankel-tensors target TR-14. The known generic Vandermonde rank value mentioned in the source is background; it need not be added as a stronger conjunct to the original equality question.

## Concrete tensor and width definitions

Use zero-based indices: the tensor associated with `h : Fin (m*(n-1)+1) -> Complex` has entry h(sum of its m indices), for index tuples `Fin m -> Fin n`. Reuse the reviewed TR14 Hankel construction and exact width definitions, retaining the complete local import closure in the final review.

An ordinary width-r decomposition means an actual sum of r arbitrary products of m complex vector entries. A symmetric width-r decomposition means an actual sum of r complex coefficients times v to the mth tensor power. Zero coefficients/vectors permit padding, so each width predicate means rank at most r, including the zero tensor at r=0.

For Vandermonde width r, require complex scalars c_j and pairs (a_j,b_j), each pair not (0,0), with v_j(i)=a_j^(n-1-i)*b_j^i for i=0,...,n-1, and H=sum_j c_j v_j^(tensor m). This includes a=0 or b=0 individually and the projective point at infinity. Coefficients may be zero, allowing width padding with e.g. (a,b)=(1,0). Do not restrict to v=(1,t,...,t^(n-1)), distinct nodes, nonzero coefficients, real data or nonnegative weights.

Ordinary border width r means there exists a sequence of arbitrary complex tensors T_l, each admitting ordinary width r, with every coordinate converging to the corresponding coordinate of H as l tends to infinity. Symmetric border width uses symmetric width r for every T_l. It thereby stays in symmetric tensor space. Ordinary approximants are **not** required to be symmetric or Hankel; symmetric approximants are **not** required to be Hankel or Vandermonde. Convergence is usual complex Euclidean entrywise convergence, not Zariski closure or exact equality at a finite index.

On each h in the chosen open set, express equality of all five ranks by all natural thresholds r: ordinary width r iff symmetric width r, ordinary width r iff ordinary border width r, ordinary width r iff symmetric border width r, and ordinary width r iff Vandermonde width r. Padding makes this equivalent to equality of the minima. Decomposition minima exist for these Hankel tensors: ordinary tensor products span the ambient tensor space, symmetric pure powers span the symmetric space over Complex, and homogeneous binary powers span the Hankel coefficient space. Border minima exist since constant sequences give a finite upper bound. No arbitrary rank function or rank oracle occurs.

## Exact nonempty Zariski-open domain

It is enough, equivalently, to existentially choose one multivariate polynomial p in the D=m(n-1)+1 Hankel coefficients such that p evaluates nonzero somewhere, and require the all-width rank equalities for every h where p(h)!=0. This is the nonempty principal open D(p). It is a concrete Zariski-open subset of the full affine coefficient space. Conversely every nonempty affine Zariski-open set contains a nonempty principal open: its complement is a common zero set, and at a point outside it at least one defining polynomial is nonzero. Thus this formulation preserves existence of a nonempty Zariski-open set without strengthening to every Hankel tensor or to one prescribed generic set.

Use actual `MvPolynomial` evaluation over Complex, not an arbitrary topology/Generic predicate. Nonemptiness must be explicit by an h witness. Quantify p and its witness after m,n but before all h/r. Neither dimension nor order can be fixed to sampled small cases.

## Review checks and computation

Review all five width predicates, the unstructured ordinary limiting sequences, infinity in the Vandermonde family, both parity/lower-bound guards, and the principal-open equivalence. No experiments or numerical certificates are required. Retain exact sum-of-indices bounds and all coefficients. The known explicit generic rank formula or a Koszul lower bound may be useful later proof data but is not a substitute for the complete original equality statement.

## Formal verification boundary

The implementation must define a closed `Target : Prop` with concrete mathematical semantics, without assuming Target or proving it by placeholder. All imported mathematical meanings require final independent review. The shared pinned LeanCert package uses kernel trust, with `#assert_statement` and `#assert_trust kernel` on Target. Frozen-boundary Comparator identity checks establish correspondence only; they do not prove the problem. No numerical computation is needed merely to state this universal target.
