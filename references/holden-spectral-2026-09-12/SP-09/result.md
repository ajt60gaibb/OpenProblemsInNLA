# SP-09 — finite amplification for a two-point spectrum

**Author:** Sidney Holden  
**Affiliation:** Center for Computational Biology, Flatiron Institute, Simons Foundation.  
**Submission date:** 12 September 2026.  
**Editorial record:** [Attribution, independent review and scope](../README.md).

The review statements below describe the supplied draft; the linked submission record records subsequent independent review.

**NEW PARTIAL RESULT** relative to the scope explicitly listed in the pinned
README; the theorem may already be known elsewhere. No novelty claim is made.

The original target is: for every n>=3, finite k>=2 and normal A,B in C^{n x n},
with delta_n(A,B)=min_{U*U=I}||A-U*BU||_2 and A^(k)=I_k tensor A, prove or
refute delta_{nk}(A^(k),B^(k))=delta_n(A,B). The norm is the spectral norm, not
Frobenius norm, and the larger unitary is unrestricted.

`proof.md` proves equality whenever at least one of A,B has at most two distinct
eigenvalues, with arbitrary multiplicities and no restriction on the other
normal spectrum. It first proves that the orbit distance equals the bottleneck
matching distance on this subclass. A threshold characterization with two
capacity counts is invariant under multiplying all multiplicities by k.

This genuinely includes non-self-adjoint pairs, e.g. a two-point spectrum on one
side and a noncollinear complex spectrum on the other. It does not establish
the equality when both sides have at least three distinct eigenvalues.

**Status proposal: retain PARTIAL; document this subclass after verification and
prior-art checking.** The original all-normal target is not resolved.
