# Rook pivoting: recovered lower-bound family

This is **partial research**, not one of the eight candidate resolutions. No matching general upper bound is supplied.

The earlier mathematical notes contain the real matrix family

$$
A(t)=\begin{pmatrix}
1&0&-1/3&1&1\\
0&1&1&-1&1\\
1&-1/3&1&t&-1\\
-1&1&t&1&-1\\
-1&-1&1&1&1
\end{pmatrix}.
$$

Its diagonal elimination pivots, when defined, are

$$
1,\quad 1,\quad \frac53,\quad
3-\frac{(3t-4)^2}{15},\quad
\frac{27t^2-42t-217}{9t^2-24t-29}.
$$

For this reconstruction, the rational parameter $t=1/6$ was selected and checked independently using exact arithmetic. The initial largest entry modulus is one. The pivots are

$$1,\quad 1,\quad \frac53,\quad \frac{131}{60},\quad \frac{893}{131}.$$

At every step the displayed diagonal pivot is maximal in modulus in **both its active row and its active column**. It is therefore an admissible rook pivot under the convention allowing any such pivot and allowing ties. No row or column exchanges are needed for this path. The largest intermediate entry is $893/131$, and the nonzero pivots certify nonsingularity. Consequently this gives a finite lower bound of $893/131$ for the worst permitted order-five growth under that convention.

Run `python3 verification/rook_partial.py` for the complete rational factorization and pivot checks. The output is `verification/rook_results.json`.

This example does not establish that $893/131$ is optimal. It does not address a particular implementation's deterministic tie-breaking rule unless that implementation follows the displayed permitted path. Earlier summaries also mentioned a small-order upper-bound proof and additional examples; those specific arguments have not been recovered into this package and are not claimed here.
