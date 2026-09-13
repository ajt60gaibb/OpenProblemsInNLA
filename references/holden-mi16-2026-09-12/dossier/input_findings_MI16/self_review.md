# Self-review

The critical step is the symmetric multiaffine maximizer lemma. The proof uses a maximizer of minimum support; without that choice, the B=0 case would leave a gap. All complex phases cancel in the permanent expansion because each permutation uses the same selected index set in rows and columns.

Checked: n=1; alpha=beta; alpha=0; beta=0; alpha<beta; the all-zero spectrum; zero coordinates of u; equality of the prescribed spectrum for every explicit candidate. Negative delta causes no sign error because the support lemma allows arbitrary real coefficients.

`verify_exact.py` checks the permanent expansion against permutation enumeration with rational matrices, the formula on every equal-support candidate, and exact sample-grid upper bounds. These finite tests supplement, and do not replace, the mathematical proof of the maximum.

No proof for general eigenvalue lists, novelty determination, external peer review, or formal proof-assistant verification is claimed.
