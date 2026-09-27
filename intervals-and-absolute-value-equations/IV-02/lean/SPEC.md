# IV-02 statement specification

Source correspondence: `04_twenty_problem_resolutions/main.tex`, section
`sec:intervals`, theorem `thm:iv-det`; canonical source snapshot
`sources/aa8d010bdd5a/intervals-and-absolute-value-equations/IV-02/README.md`.

## Canonical computational target

For `n >= 2`, the input is `3*n-2` closed real intervals with rational
endpoints: diagonal `[a_lower_i,a_upper_i]`, upper diagonal
`[b_lower_i,b_upper_i]`, and lower diagonal `[c_lower_i,c_upper_i]`, all with
lower endpoint at most upper endpoint. The family `T` contains exactly the
real tridiagonal matrices with those independent entry intervals and zeros
outside the three diagonals. The exact outputs are rational

`d_- = min_{T in family} det(T)`, `d_+ = max_{T in family} det(T)`.

The original question asks for a deterministic algorithm polynomial in total
binary input length, uniformly in `n`, including singular matrices and
intervals crossing zero. The paper resolves this computationally: deciding
whether `max det(T) >= rational threshold` is NP-complete even when every
matrix is nonsingular and every superdiagonal entry is fixed to `1`; exact
determinant-range computation is NP-hard. The exact-output task is in
`FP^NP`, and the paper claims a polynomial-time exact algorithm exists iff
`P=NP`. No unconditional `P != NP` claim is made.

## Reduction data and all numerical claims

From positive integer PARTITION weights `w_1,...,w_m`, set
`W=sum_i w_i`, `delta=1/(10*W^2)`, `t_i=delta*w_i`,
`c_i=(1-t_i^2)/(1+t_i^2)`, `s_i=2*t_i/(1+t_i^2)`,
`theta_i=2*arctan(t_i)`, and `N=4*m-2`. The companion layers have
`M(a,beta)=[[a,-beta],[1,0]]`, with the four displayed layer types in the
paper; the `m-1` uncertain entries are `q_i in [-1,1]`, independently.

At vertices, `epsilon_i=-q_i in {-1,1}` and endpoint determinants are
`cos(sum_i sigma_i*theta_i)` for sign vectors `sigma_i in {-1,1}` with
`sigma_m=1`. The proof requires `c_i^2+s_i^2=1`,
`0 <= 2*t-2*arctan(t) <= (2/3)*t^3`,
`E=sum_i |theta_i-2*delta*w_i| <= delta/(150*W) <= delta/10`,
`sum_i theta_i <= 1/(5*W) <= 1/5`, and positivity of every determinant.

If PARTITION is satisfiable, `max det >= 1-delta^2/200`. If it is not,
every signed weight sum has absolute value at least one,
every endpoint angle has absolute value at least `19*delta/10`, and
`max det <= 1-(361/300)*delta^2 < 1-delta^2`. The rational separating
threshold is `tau=1-delta^2/2`. All constructed entries have polynomial
binary length, so the reduction is polynomial.
