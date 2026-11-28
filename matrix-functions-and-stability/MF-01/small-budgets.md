# Exact sign approximation for small multiplication budgets

Let $`e_s(\delta)`$ be the uniform minimax sign error over real odd
polynomials of degree at most $`2s-1`$ on the set $`I_\delta`$ in
[MF-01](README.md#problem-statement). Then for every $`0<\delta<1`$,

```math
E_0(\delta)=E_1(\delta)=e_1(\delta),\qquad
E_2(\delta)=e_2(\delta),\qquad E_3(\delta)=e_4(\delta).
```

A product of previously available polynomials at most doubles the
maximum degree, so a budget of $`m`$ gives degree at most $`2^m`$.
The odd part of any polynomial has no larger sign error on the symmetric
set $`I_\delta`$, by the triangle inequality and oddness of sign. This
gives all four lower bounds. Linear polynomials have zero cost, and
every odd cubic uses only the products forming $`x^2`$ and $`x^3`$.
For $`m=3`$, we prove that every polynomial of degree exactly eight has
a three-product evaluation. Consequently a polynomial of degree at most
seven lies in the coefficient-space closure of the three-product set,
by adding $`\varepsilon x^8`$ and sending $`\varepsilon`$ to zero. This is
sufficient for the infimum since convergence is uniform on $`I_\delta`$.

## Three products evaluate any real octic

Normalize the leading coefficient to one. Let $`p_i`$ be the coefficients
of the resulting polynomial. The first two products form $`x^2`$ and
$`Q=x^2(x^2+a x)`$. Set $`a=p_7/2`$. The third product will be

```math
\bigl(Q+u x^2+v x\bigr)\bigl(Q+u' x^2+v' x\bigr).
```

Set $`S=u+u'=p_6-a^2`$ and $`T=v+v'=p_5-aS`$ to match degrees six
and five. Put $`u=S/2+1`$ and $`u'=S/2-1`$. Write $`v=T/2+b`$ and
$`v'=T/2-b`$ with $`b`$ to be chosen. The degree-four coefficient is
$`aT+uu'`$, independent of $`b`$. Adding $`hQ`$ with
$`h=p_4-aT-uu'`$ matches degree four. The resulting degree-three
coefficient is $`ST/2-2b+ah`$, so choose $`b`$ to match $`p_3`$.
Free additions handle degrees zero through two. All scalar parameters
are real, and the leading coefficient can be restored at zero cost.

## Values and uniform dependence on the gap

For $`s=1`$ the minimax polynomial is $`2x/(1+\delta)`$, giving
$`e_1=(1-\delta)/(1+\delta)`$. For $`s=2`$ set

```math
K=1+\delta+\delta^2,\qquad A=\delta(1+\delta),\qquad B=2(K/3)^{3/2}.
```

The minimax cubic is $`p(x)=2x(K-x^2)/(A+B)`$. On $`[\delta,1]`$
the two endpoints give the same value $`2A/(A+B)`$ and the sole interior
extremum, at $`\sqrt{K/3}`$, gives $`2B/(A+B)`$. The three errors alternate
with equal absolute value. Any strictly better odd cubic would differ
from $`p`$ with alternating signs at these three positive points, which
would force two distinct positive roots. A nonzero odd cubic has at most
one strictly positive root. Hence $`e_2=(B-A)/(B+A)`$.

Here are explicit bounds for any positive integer $`s`$. Define
$`a_s=(2s-1)!!/2^s`$ and
$`b_s=(\int_0^1(1-t^2)^{s-1}\,dt)^{-1}`$. Then

```math
\frac{a_s(3/4)^s}{2^{s+1}s^s}(1-\delta)^s
\ \le\ e_s(\delta)\ \le\
\frac{b_s 2^{s-1}}{s}(1-\delta)^s.
```

The upper bound uses $`p_s(x)=b_s\int_0^x(1-t^2)^{s-1}\,dt`$ and
$`1-t^2\le2(1-t)`$ on $`[0,1]`$. For the lower bound write a competing
odd polynomial as $`xq(x^2)`$ with $`\deg q\le s-1`$. If its sign error
is $`E`$, then $`|q(u)-u^{-1/2}|\le E/\delta`$ for
$`u\in[\delta^2,1]`$. Take the $`s`$th forward difference on the equally
spaced grid of $`s+1`$ nodes of spacing $`(1-\delta^2)/s`$. It kills
$`q`$ and has absolute value at least
$`a_s((1-\delta^2)/s)^s`$ on $`u^{-1/2}`$, as follows by the iterated
integral formula for the difference and the constant sign of the
$`s`$th derivative. The absolute sum of the difference coefficients is
$`2^s`$, proving $`E\ge\delta a_s((1-\delta^2)/s)^s/2^s`$. This gives the
displayed result for $`\delta\ge1/2`$. Otherwise use monotonicity in
$`\delta`$ and the same estimate at $`1/2`$.

## One larger-budget upper bound

The same $`p_s`$ at $`s=21`$ is $`xq(x^2)`$ for a polynomial $`q`$ of
degree 20. The exact five-product construction in [MF-25](../MF-25/README.md#five-products-cover-degree-20-exactly)
therefore evaluates it with seven products, including $`x^2`$ and the
final factor $`x`$. It maps $`[0,1]`$ to itself and is increasing there.
If $`C=b_{21}2^{20}/21`$, then $`1-p_{21}(x)\le C(1-x)^{21}`$. Iterating
the seven-product polynomial $`\ell=\lfloor m/7\rfloor`$ times
(the zero-fold iteration is $`x`$) gives the explicit upper bound

```math
E_m(\delta)\le C^{-1/20}\bigl(C^{1/20}(1-\delta)\bigr)^{21^{\ell}}.
```

This bound decays with $`m`$ when $`C^{1/20}(1-\delta)<1`$.
