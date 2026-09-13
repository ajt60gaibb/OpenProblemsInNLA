# Notes — SP-03

The multiplier K must satisfy K^T=-K, and the rational reconstruction of X uses
Q=I+K^2. Counting the cleared quartics without saturation by det(Q) is invalid:
it can count denominator-zero components that are not critical points.
The dimension argument concerns the image of actual critical pairs (X,K), not
all extraneous solutions of the cleared equations.

The generic count is still missing. A special-data calculation would need a
separate proof of genericity; nonsingular isolated roots at one point do not by
themselves rule out solutions lost at infinity. A promising next step is an
exact saturated computation for a new rank, with a rigorously justified
specialization or degree certificate. No such computation was completed here.

The original scope and all-rank conjecture are in `result.md`; all substantive
proof work is preserved in `proof.md`. The order-one example is a known check,
not a new partial resolution. No failed numerical search is being presented as
an algebraic nonexistence proof.
