# Proof and model audit

This file is a compact guide to checking the complete proof in `solution.pdf` and `solution.tex`. It is not a separate formal verification.

## 1. Exact quantifiers and model

The input A and all M candidate matrices are fixed before randomness. The success probability is instance-wise. Both right and left matvecs are charged. Every vector, every side, and the exact-versus-sketch branch are chosen before receiving any answers. No upper bound on OPT, ||A||, or the candidate norms is used. Candidate processing is unrestricted, as in RE-06.

## 2. Gaussian lower-tail lemma

Use lambda_i = sigma_i(C)^2, T = sum_{i>r} lambda_i, and a = lambda_{r+1}. For T = 0 the strict lower-tail event is empty. Otherwise a > 0. The Chernoff parameter is theta = eta/(2a). The first r singular values each contribute at least log(1 + eta) to the log-determinant term. For the remaining values,

    sum_{i>r} log(1 + 2 theta lambda_i)
       >= 2 theta T - 2 theta^2 a T.

The resulting exponent is at most

    -s eta^2 T/(4a) - (s r/2) log(1 + eta)
       <= -s r eta/4.

There is no assumption on stable rank, condition number, or the norm of C.

## 3. The only candidate-wise union bound

Apply that lower-tail lemma to the M fixed residuals A - B. Apply an upper-tail bound only to the one fixed optimal residual. The first-sketch minimizer therefore has a small rank-r tail. Its full residual can be arbitrarily larger; the proof never treats it as a constant-factor approximation.

## 4. Independence after candidate selection

B0 is a function of the first sketch G0 and AG0 only. Conditional on those data, C = A - B0 is fixed and the reconstruction matrices G1 and H retain their independent Gaussian distributions. The fact that their answers were collected earlier does not change that distributional statement, because they are not consulted in selecting B0. Repair is analyzed once conditionally, not M times.

## 5. Deterministic range majorant

With Omega_1 = V_1^T G1 and Omega_2 = V_2^T G1, Omega_1 has full row rank almost surely. The explicit approximation

    C G1 Omega_1^dagger V_1^T

belongs to range(C G1), and its squared error is exactly

    tau_r(C)^2 + X,
    X = ||Sigma_2 Omega_2 Omega_1^dagger||_F^2 >= 0.

This derivation does not invert Sigma_1. It remains valid when C is rank-deficient or rank(C) < r. Orthogonal projection onto range(C G1) can only improve its error.

## 6. Regression error and the Markov pitfall

For R = (I - Q Q^T) C,

    ||C - C_hat||_F^2 = ||R||_F^2 + V,
    V = ||(H^T Q)^dagger H^T R||_F^2 >= 0.

This is an exact orthogonal decomposition, not a triangle-inequality estimate. Conditional on Q, Gaussian coordinates along Q and Q-perp are independent. The inverse moment gives

    E_H V = d/(ell - d - 1) ||R||_F^2,

where d = rank(C G1) <= k. The proof uses the nonnegative majorant Z = X + V. It does not apply Markov directly to error^2 - tau_r(C)^2, which can be negative when the output rank exceeds r.

## 7. Pseudoinverse denominators

For a d-by-p standard Gaussian matrix, p > d + 1,

    E ||X^dagger||_F^2 = d/(p - d - 1).

The Schur-complement residual has chi-square degrees of freedom p - d + 1. Taking its reciprocal reduces the denominator by two, giving p - d - 1, not p - d or p - d + 1. The note derives this moment directly.

## 8. Explicit failure budget

The parameter choice guarantees:

    first-sketch uniform lower tail: <= M exp(-8L) <= 2 exp(-16)
    optimal-residual upper tail:     <= exp(-8)
    conditional repair:             < 1/128 + 1/524288

Their sum is 0.008150095046884763, below 0.01. The two main success events need not be independent; a union bound is sufficient.

## 9. Approximation factor

On the success events,

    ||A - A_tilde||_F <= (1 + eta)/sqrt(1 - eta) OPT
                       <= (1 + 2 eta) OPT,

because eta < 1/8 and

    (1 + 2 eta)^2 (1 - eta) - (1 + eta)^2
      = eta (1 - eta - 4 eta^2) >= 0.

Nearest-family selection then gives

    ||A - B_hat||_F <= OPT + 2 ||A - A_tilde||_F
                     <= (3 + 4 eta) OPT
                     = (3 + epsilon) OPT.

## 10. Query count and small dimension

Every call appears in the precommitted list: s columns of A G0, k columns of A G1, and ell columns of A^T H. No A^T Q query occurs. The rounded parameters satisfy

    N <= 66403 r/eta^2,
    r < 3 sqrt(log(2M)),
    eta^(-2) = 16 epsilon^(-2).

Therefore N <= 3,187,344 sqrt(log(2M)) epsilon^(-2), below the stated 4,000,000 constant. If n <= N, the algorithm precommits instead to n standard-basis right queries. Thus the actual count is min(n, N).

## 11. Degenerate cases

The zero-tail lower-tail event is empty. Zero range dimension uses C_hat = 0. The Gaussian full-rank claims hold almost surely and pseudoinverses are defined on the null-probability exceptions. OPT = 0 is never used as a denominator. If A belongs to F, the finite first-sketch minimization identifies it almost surely; the exact branch also returns it. Fixed tie-breaking is used throughout.

## 12. Status of implementation checks

The code performs floating-point SVDs and numerical rank decisions with pseudorandom samples. These are not the exact primitives of the theorem. The numerical audits exercise the identities and query schedule but cannot establish the all-input theorem. The smaller experimental widths are deliberately not labeled theorem-sufficient. No outside review or proof-assistant validation is claimed.
