# TR-04 statement specification

Source correspondence: `04_twenty_problem_resolutions/main.tex`, section
`sec:tr04`, theorem `thm:tr04-main`; canonical source snapshot
`sources/aa8d010bdd5a/tensor-computations/TR-04/README.md`.

## Complete target

Let `d >= 3`, each mode size `n_1,...,n_d >= 2`, and each prescribed rank
`r_1,...,r_(d-1)` a positive integer. Let `S_r` be the tensors in
`R^(n_1 x ... x n_d)` whose unfolding across every cut
`1,...,j | j+1,...,d` has matrix rank at most `r_j`. For a dense real tensor
`A`, define

`E_*(A,r) = min { ||A-Y||_F^2 : Y in S_r }`.

The minimum is attained. The arithmetic/SVD model is exact: arithmetic,
singular subspaces and equality tests for singular values are exact. A
deterministic algorithm, polynomial in dense input size and rank parameters,
must return `X in S_r` with

`||A-X||_F^2 < (d-1)*E_*` when `E_* > 0`,
and `X = A` when `E_* = 0`.

It tests at most `n_1` first-cut singular-subspace choices, uses at most
`n_1` ordinary TT-SVD completions, and never increases a prescribed rank.

## Proof-critical definitions and constants

For the first unfolding `A_(1)`, define
`e^2 = sum_{i>r_1} sigma_i(A_(1))^2`, with out-of-range singular values zero;
the proof requires `e^2 <= E_*`. In the tied singular-value case, let `tau`
be `sigma_(r_1)(A_(1)) > 0`, let `H` be the left singular subspace with
singular value strictly greater than `tau`, let `E` be the `tau`-eigenspace,
`h=dim H`, `t=dim E`, `s=r_1-h`, and `1 <= s <= t`. For a deterministic
orthonormal basis `u_0,...,u_(t-1)` of `E`, use cyclic windows
`W_j=span{u_j,...,u_(j+s-1)}` (indices modulo `t`) and
`P_j=P_H+P_(W_j)`. Each vector occurs in exactly `s` windows and
`(1/t) sum_j P_(W_j) = (s/t) P_E`.

The completion lemma must retain, for any orthonormal `U` spanning a tested
first-mode subspace and `P=UU^T`,
`||A-X_U||_F^2 <= ||(I-P)A||_F^2 + (d-2)||P(A-Y)||_F^2`
for every `Y in S_r`. In the equality case `e^2=E_*>0`, the residual of an
optimal `Y` is annihilated by `P_H`, and the cyclic average gives a candidate
with factor `1+(d-2)*s/t < d-1`. The `s=t` case is included separately.

## Explicit limitation retained

The theorem is pointwise strict; there is no uniform constant smaller than
`d-1` asserted. The fixed `3 x 3 x 2`, ranks `(2,1)` example with
`A = alpha e1⊗e1⊗f1 + beta e2⊗e2⊗f1 + gamma e3⊗e3⊗f2`,
`alpha > gamma >= beta > 0`, has `E_* = gamma^2` and ratio
`1+(beta/gamma)^2`, tending to `2=d-1` as `alpha=2`, `beta=1`,
`gamma downarrow 1`. The formal result must not be strengthened to a uniform
strict factor or a finite-precision theorem.
