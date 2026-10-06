# Final growth scalar absorption: preimplementation contract

The independent mathematical reviewer proposed, and root explicitly approved before code, this stronger uniform real contract. For D>=0, a>=1, N>=1, y>=1, r=ceil(y), x=a*y^2, and tau=(2N/r)*exp(12D*y), set

K=2^(5r)*sqrt(1+(2+4x)tau)*(1+sqrt(8r+4x)*sqrt(3exp(2+x/r)/r)).

Then sqrt(2x*K^2)<=sqrt(N)*exp(C*y), for a positive C depending only on D,a. Specialize N=n and y=sqrt(log n) whenever log n>=1, which holds eventually. There is no probability, determinant, or singular-value premise in this scalar module, and no numerical search or giant threshold evaluation.

The approved route uses y<=r<=2y. Then tau<=2N exp(12Dy), the first square-root factor is at most sqrt(1+12a)*sqrt(N)*y*exp(6Dy), and the final smoothing factor is at most (1+sqrt(60a))*y*exp(1+ay/2). The power of two is at most exp(10y). Thus the full expression is at most B*sqrt(N)*y^3*exp((10+6D+a/2)y), where B=exp(1)*sqrt(2a)*sqrt(1+12a)*(1+sqrt(60a)). Since y^3<=exp(3y) and B<=exp(B*y), the explicit choice C=20+6D+a+B is sufficient and positive.

Root checked these exact intermediate inequalities and this explicit constant, and approved implementation before any Lean source was written. The stronger real version requires only N>=1 (no relation between N and y). The original square-root growth target is unchanged.

## Completed implementation

Frozen source SHA-256: `b1c504dbf41a44545243d2e287920f75ab9b13524889f93ca5cbee62d562738c`. The module implements the exact literal `cap`, positive explicit `constant`, the stronger `real_absorption`, its `log_absorption` specialization for log(n)>=1, and `eventual_absorption` with the original natural-dimensional parameters. Rounding is bounded by y<=ceil(y)<=2y; no explicit large natural threshold is evaluated. All 13 declarations have individual kernel trust assertions and axiom prints. The local pinned build completed cleanly with only foundational axioms; scope-qualified receipt and log are in `final-growth-scalars/`. Root's independent final source review is separate.
