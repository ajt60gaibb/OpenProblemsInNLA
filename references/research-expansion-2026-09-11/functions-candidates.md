# Matrix functions and pseudospectra: source audit

Checked September 11, 2026. See the [admission record](README.md) for the
final statements, ratings and exports.

## Admitted targets

- [MF-23: complete Crouzeix](../../matrix-functions-and-stability/MF-23/README.md).
  Crouzeix (2007) introduced the complete target. Equation (1.2) and Theorem 1.1
  of [arXiv:2608.27346v3](https://arxiv.org/html/2608.27346v3), September 9,
  explicitly distinguish it from scalar proofs. Arbitrary polynomial block
  size is essential; square blocks cover rectangular ones by zero padding.
- [SP-15: finite unitary classes](../../eigenvalues-and-inverse-problems/SP-15/README.md).
  Fortier Bourque–Ransford (2009), Theorem 1.4 and §6.2, and
  [Ransford (2010), Theorem 5.4 and pp.10–11](https://analyse.mat.ulaval.ca/abstracts/2010-01.pdf)
  ask whether the exceptional set can be empty. The canonical pigeonhole
  statement is equivalent to a bound on the number of classes. Ordinary
  similarity, proved in later work, does not imply unitary similarity.
- [MF-24: uniform polynomial-norm comparison](../../matrix-functions-and-stability/MF-24/README.md).
  Fortier Bourque–Ransford (2009), p.513 after Theorem 1.3, explicitly ask for
  a dimension-independent bound. [Ransford–Walsh, v2](https://arxiv.org/pdf/2109.14472v2),
  Theorem 1.3, gives the strict square-root-of-dimension-minus-two estimate;
  Proposition 5.1 shows the sharp supremum in dimension four. The original
  square-root-of-dimension sharpness question has been superseded, so it is
  not the admission target. Vanishing of either polynomial matrix implies
  vanishing of the other, making the ratio and inequality formulations equivalent.

The two super-identical-pseudospectral questions were checked against later
similarity and norm papers and targeted proof/counterexample searches. No
full solution was found. Their older source statements and bounded status
evidence are explicitly disclosed on the canonical pages.

## Related extension retained without a new ID

The completely bounded Clouâtre–Ostermann–Ransford conjecture is a broader
operator-algebra implication. Its original statement is Conjecture 6.1 in
[arXiv:2011.10422v2](https://arxiv.org/pdf/2011.10422v2), published in Journal
of Operator Theory 90 (2023), 209–221
([DOI](https://doi.org/10.7900/jot.2021nov15.2364)). It asks whether a unital
completely bounded homomorphism has completely bounded norm at most two
when its average with an adjoint antilinear completely contractive map is
completely contractive. All the original map and matrix-norm assumptions
matter.

The September 9 manuscript above explicitly retains this complete abstract
question. Its low-dimensional quotient-uniform-algebra result and
[Hartz–McCarthy, arXiv:2606.02922](https://arxiv.org/html/2606.02922v1),
Theorem 1.2, settle restricted settings. The scalar claim in
[Badea–O'Loughlin–Virtanen, arXiv:2609.03637](https://arxiv.org/html/2609.03637v1)
is not a complete resolution. This broader extension was not given a
separate ID in this batch because MF-23 supplies the direct matrix-function
question; the implication and literature are retained here for future review.
