# Self-review — KE-02

**Outcome:** no gap found in the two subclass proofs during this self-review.
This is not an independent referee report.

The strongest remaining issue for a status update is **scope and significance**,
not a hidden completion claim: the proof still excludes most arbitrary
tridiagonal inputs. Only OPEN -> PARTIAL is proposed, subject to review.

Checked: n=2; r=0; r=delta/(4n); equal diagonals and sorting ties; arbitrary
complex phases; all 0<delta<1/2; zero off-diagonal entries in Theorem A;
placement of D in original indices; and exact universal constants a=3,c_0=1,q=1
for Theorem B. Since delta/n<1, Theorem A also satisfies the weaker exponent-3
bound when combining the subclass algorithms.

The critical analytical chain is:
1. the quadratic-form perturbation estimate (1);
2. gauge reduction by a diagonal unitary, used only in the proof;
3. ordering of all sine eigenvalues, not only an asymptotic expansion;
4. minimum adjacent spacing at the ends of the cosine grid;
5. sin(x)>=2x/pi on the full required interval, including n=2;
6. (n+1)^2<=3n^2 and delta>=delta^3.

No numerical eigenvalue computation enters either proof. Tests are diagnostic
only. No calculation of a norm, eigenbasis, angle or logarithm is required by the
algorithm. A comparison sort suffices for Theorem A and uses no exact-input bit
extraction. Theorem B works with squared magnitudes and does not require a
transcendental primitive or even square roots.

The prior greedy construction was also checked: its induction bounds each
y_j between t_{pi(j)}-delta and t_{pi(j)}+delta. It remains in
`prior_weak_coupling_proof.md` for provenance but is not needed for Theorem B.
