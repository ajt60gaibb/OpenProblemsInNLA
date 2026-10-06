# Independent preimplementation review — approved

Reviewer: `/root/infrastructure`. Contract SHA256: `b367bd3a8b27e1b44a27cd9d41f6f59d9c21953d49040679273c1192f826c050`.

Reviewed before implementation of GaussianFutureWindow, GaussianAdaptiveFuture,
GaussianFutureSmoothing, and the stage integration. Exact threshold agrees with
GaussianSmoothing at s=4r, L=2^(4r), and zeta²=1+(2+4x)tau. The retained row
identity coordinate is disjoint from all selected coordinates. Thus the row
cost is at most n exp(-x), and the future cost is (n+1) exp(-x). The order weights
sum to one, retaining 2n+1. The nonsingular-input event justifies actual pivot
operations, annihilation, and row-l1 bounds; no future-success conditioning.

The suffix partition and explicit assembly preserve original columns and their
product law, including s=0. Fixed-fiber inverse and frame choices introduce no
measurable-selector premise. Early stages u<=5r use the proved deterministic
row-l1 bound; later stages use t=u-4r>r. This branch was also independently
approved by `/root/independent_math_review`.
