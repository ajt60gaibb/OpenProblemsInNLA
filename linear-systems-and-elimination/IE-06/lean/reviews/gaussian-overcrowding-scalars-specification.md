# Gaussian overcrowding scalar contract

Root proposed these exact scalar contracts to the independent reviewer before
implementation, under the already independently approved overcrowding moment
proposal. Define q=(j+3)/4 and r=j+1-2q in natural arithmetic. For n>j>=4,
q,r>=1, r<=n-2q, 2q+r=j+1, and 8qr>=j^2. Prove factorial inverse <=(e/q)^q
for q>=1, and binomial(m,r)<=(e*m/r)^r for r>=1. If d>2q, prove
product_(a<q)(d-2(a+1))>=q!, hence its inverse <=(e/q)^q.

With N=binomial(n-2q,r), theta in (0,1], and t=j*theta/(4e*sqrt(n)),
prove N*(e/q)^(rq)*N^q*t^(2rq)<=n^(j+1)*theta^(j^2/4).
The RHS uses real power; the LHS uses natural powers. All division denominators
are proved positive, and all integer subtractions occur under proved bounds.
These arithmetic lemmas do not assert any matrix probability estimate.
