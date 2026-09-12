# Exact optimized handicap of a cyclic three-dimensional family

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation.

## Status and relevance

This is a complete proof candidate for the explicit family below, not a solution
or a complexity lower bound for AV-03. It quantifies one obstruction to obtaining
a general polynomial-input-length bound from a handicap-dependent algorithm.
The family is itself easy to solve, and its corresponding AVEs are covered by
`hessenberg_solver.py`. Historical novelty of this formula has not been established.

We use the definition in E.-Nagy and Végh, *Handicap reduction for linear
complementarity problems*, arXiv:2605.10701v2, §1:

\[
\widehat\kappa(M)=\inf\{\kappa\ge0:
 (1+4\kappa)\sum_{v_i>0}v_i+\sum_{v_i<0}v_i\ge0
 \text{ for every }x\in\mathbb R^n,\quad v_i=x_i(Mx)_i\},
\]
\[
\kappa^*(M)=\inf_{D\text{ positive diagonal}}\widehat\kappa(DM).
\]

Source: https://arxiv.org/html/2605.10701v2 . The proof below is independent of
any algorithm or convergence theorem in that source.

## Theorem

Let
\[
 P=\begin{pmatrix}0&1&0\\0&0&1\\1&0&0\end{pmatrix},
 \qquad M_a=I+aP,\qquad a\ge0.
\]
Then
\[
 \boxed{\quad\kappa^*(M_a)=\widehat\kappa(M_a)
      =\max\{0,(a^2-4)/16\}.\quad}                 \tag{1}
\]
All proper nonempty principal minors of \(M_a\) equal 1 and its determinant
is \(1+a^3\); consequently it is a P-matrix for every \(a\ge0\).

### Lower bound, including every positive row scaling

For \(a>0\), set \(D=\operatorname{diag}(d_1,d_2,d_3)\), with all \(d_i>0\).
At \(x=(1,-2/a,0)^T\), the three products \(x_i(DM_ax)_i\) are
\[
 (-d_1,\;4d_2/a^2,\;0).
\]
Thus every admissible \(\kappa\) satisfies
\[
 1+4\kappa\ge {a^2\over4}{d_1\over d_2}.
\]
Cyclically rotating the test vector yields the other two ratios
\(d_2/d_3\) and \(d_3/d_1\). Multiplying the three inequalities and taking
the positive cube root gives
\[
 1+4\kappa\ge a^2/4.
\]
This proves the lower bound in (1), uniformly over all positive diagonal \(D\),
when \(a\ge2\); nonnegativity of \(\kappa\) supplies the remaining lower bound.

### Upper bound for \(0\le a\le2\)

Here
\[
 x^TM_ax=(1-a/2)\sum_i x_i^2+(a/2)(x_1+x_2+x_3)^2\ge0.
\]
Therefore \(\widehat\kappa(M_a)=0\).

### Upper bound for \(a\ge2\)

Write \(c=a^2/4\ge1\). We prove
\[
 c\sum_{v_i>0}v_i+\sum_{v_i<0}v_i\ge0.            \tag{2}
\]
If all coordinates of \(x\) have the same weak sign, all \(v_i\ge0\).
Otherwise, by a cyclic permutation and possibly multiplication of the whole
vector by \(-1\), write \(x=(p,-q,r)^T\), where \(p,q,r\ge0\). This also
covers zero coordinates and all mixed-sign patterns. Then
\[
 v_1=p^2-apq,\quad v_2=q^2-aqr,\quad v_3=r^2+arp\ge0.
\]
There are only three nontrivial cases. Products equal to zero can be assigned
to either adjacent case, because they contribute zero.

**Case 1: both \(v_1,v_2\) are negative.** We must show
\[
 F=p^2+q^2-aq(p+r)+c(r^2+arp)\ge0,
 \qquad q\le ar.                                  \tag{3}
\]
If \(p\le r\), minimization over unrestricted real \(q\) gives
\[
 F\ge (1-c)p^2+c(a-2)pr
 \ge pr\{1+c(a-3)\}
 ={pr\over4}(a-2)^2(a+1)\ge0.
\]
The second inequality uses \(1-c\le0\) and \(p^2\le pr\).
If \(p\ge r\), the unconstrained minimizing value
\(a(p+r)/2\) is at least \(ar\). The quadratic in \(q\) is decreasing on
\(( -\infty,ar]\), so
\[
 F\ge F\big|_{q=ar}=p^2+{a^2(a-4)\over4}pr+{a^2\over4}r^2.\tag{4}
\]
For \(2\le a\le4\), \(a(4-a)\le4\), so the middle coefficient in (4)
is at least \(-a\); (4) is at least \((p-ar/2)^2\). For \(a\ge4\),
every coefficient in (4) is nonnegative. This proves (3).

**Case 2: only \(v_1\) is negative.** We have \(q>0\), \(0\le r/q\le1/a\).
Put \(z=p/q\), \(y=r/q\). The required expression, divided by \(q^2\), is
\[
 H(z,y)=(z-a/2)^2+c\{y^2+a(z-1)y\},
 \quad z\ge0,\quad 0\le y\le1/a.                  \tag{5}
\]
For \(z\ge1\), the last braces are nonnegative. Suppose \(0\le z\le1\).
The unrestricted minimizing value of \(y\) is \(a(1-z)/2\).
If \(z\le1-2/a^2\), the minimum on the permitted interval is at \(y=1/a\):
\[
 H(z,y)\ge z^2+(a^2/4-a)z+1/4\ge(z-1/2)^2\ge0,
\]
because \(a^2/4-a\ge-1\) for every real \(a\).
If \(1-2/a^2\le z\le1\), the minimum is
\[
 (a/2-z)^2-{a^4\over16}(1-z)^2.                   \tag{6}
\]
For \(a=2\), (6) is zero. For \(a>2\),
\[
 z\ge1-2/a^2\ge a/(a+2)
\]
(the second difference is \(2(a-2)(a+1)/(a^2(a+2))\)). Therefore
\[
 a/2-z\ge {a^2\over4}(1-z)\ge0,
\]
which proves (6) is nonnegative. This proves (5).

**Case 3: only \(v_2\) is negative.** The inequality \(v_1\ge0\) implies
\(p=0\) or \(p\ge aq\). For \(p=0\), the required expression is
\(q^2-aqr+cr^2=(q-ar/2)^2\). For \(p\ge aq\), it is
\[
 c\{p^2+a(r-q)p+r^2\}+q^2-aqr.
\]
Its derivative with respect to \(p\) is at least \(ca(q+r)\ge0\).
Its value is consequently at least its value at \(p=aq\), namely
\[
 q^2+cr^2+(ca^2-a)qr\ge0,
\]
since \(ca^2-a=a^4/4-a\ge0\) for \(a\ge2\).

These cases prove (2), hence \(\widehat\kappa(M_a)\le(c-1)/4\).
Combining with the lower bound, and using \(D=I\) as an admissible scaling,
proves (1). No assertion about numerical optimization is used. \(\square\)

## Consequences and limits

For rational \(a=2^m\), the input length of this fixed-dimensional family is
\(O(m)\), whereas \(\kappa^*(M_a)=(4^m-4)/16\) for \(m\ge1\).
Thus even arbitrary positive row scaling cannot provide a polynomial bound
on this parameter in binary input length. Positive row-and-column scaling
cannot do better: for every positive diagonal \(E\),
\(\widehat\kappa(EME)=\widehat\kappa(M)\), by the substitution \(y=Ex\)
in the defining products. Consequently \(D_LMD_R\) has the same handicap as
\(D_R^{-1}D_LM\), by congruence with \(D_R^{-1}\).

For \(a>0\), the reverse AVE transformation gives
\[
 A=(M_a+I)(M_a-I)^{-1}=I+(2/a)P^{-1}.
\]
After reversing the cyclic order, this is the family treated by Theorem H
and the Newton-cycle example. It is regular for every \(a>0\).
This is an explicit separation between a large handicap parameter and the
actual difficulty of this structured family. It does **not** prove that the
handicap-dependent algorithm necessarily takes exponential time on the
family, and does **not** rule out a different polynomial-time general solver.
