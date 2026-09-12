# Independent scalar lemma for the IE-15 proof candidate

Let 0<p<=1, q>0, |a|,|b|,|d1|,|d2|<=1 and 0<=c1,c2<=1. Assume

    |q+pab|<=1,
    |qd2+pad1|<=1,
    |qc2+pc1b|<=1.

Put S=pc1d1+qc2d2 and G=p+q+S. Then S<=2 and G<=4.

Proof. If q<=1, S<=p+q<=2 and G<=2(p+q)<=4. Suppose q>1. The first constraint implies ab<0 and delta:=q-1<=p|ab|<=p. If d2<=0, then S<=p and G<=2p+q<=1+3p<=4. Hence assume d2>0.

If a<0<b and d1<0, the last constraint gives qc2<=1, so S<=qc2d2<=1 and G<=p+q+1<=2+2p<=4. If a<0<b and d1>=0, interchange (a,b), (c1,d1), and (c2,d2). This preserves all hypotheses, S and G, and reduces to a>0>b with the newly named c1,c2 nonnegative. Thus assume a>0>b.

Set alpha=pa, beta=p|b|. Then 0<alpha,beta<=p<=1 and alpha*beta>=p*delta. In particular, delta<=alpha,beta. Write t=c1 and u=d1. The last two constraints give

    c2<=min(1,(1+beta*t)/q),
    d2<=min(1,(1-alpha*u)/q).

As c2>=0 and d2>0, their product is bounded by the product of these upper bounds. Therefore

    S <= H(t,u)
       := p*t*u + min(q,1+beta*t)*min(q,1-alpha*u)/q.

The right side is bilinear on each rectangle cut out by t=delta/beta and u=-delta/alpha in [0,1] x [-1,1]. A bilinear function on a closed rectangle attains its maximum at a corner. It is therefore enough to evaluate the following nine values, with rows t=0,delta/beta,1 and columns u=-1,-delta/alpha,1:

    1                  1                          (1-alpha)/q
    q-p*delta/beta     q-p*delta^2/(alpha*beta)     1-alpha+p*delta/beta
    q-p                q-p*delta/alpha             p+1-alpha

Every value except the middle and bottom-right ones is at most 1, using delta<=p, delta<=p*a*|b|, and a,|b|<=1. For the middle value, H<=q<=2, and

    p+q+H <= p+2q-delta^2/p
             =2+2p-(p-delta)^2/p <=4,

where alpha*beta<=p^2 was used. For the bottom-right value, H<=p+1<=2, and

    p+q+H=2+2p+delta-alpha<=2+2p<=4.

For every other corner, H<=1 and p+q+H<=p+(1+p)+1<=4. Thus S<=2 and G<=4 in all cases. No division by a,b,alpha,beta is used before q>1 forces them to be nonzero.

Since for c,d in [-1,1]

    3cd+1+|c-d| <= 2(1+cd),

this also proves

    p*(3c1d1+1+|c1-d1|)+q*(3c2d2+1+|c2-d2|) <= 2G <=8.

Signed: independent Codex agent `/root/prepare_manuscripts`, 11 September 2026. This proves the scalar lemma; the full n=4 elimination reduction still requires separate checking.
