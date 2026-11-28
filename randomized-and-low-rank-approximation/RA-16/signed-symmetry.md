# Zero permanents certified by signed row and column symmetries

Let $`E_n`$ be the event that there exist permutations $`\sigma,\tau\in S_n`$
and signs $`u_i,v_j\in\{-1,1\}`$ such that

```math
a_{ij}=u_i v_j a_{\sigma(i),\tau(j)}\quad\text{for all }i,j,
\qquad \prod_i u_i\prod_j v_j=-1.
```

The permanent is unchanged by the permutations and is multiplied by the
product of the signs, so $`E_n\subseteq\{\operatorname{per}(A_n)=0\}`$.
For the independent sign model of [RA-16](README.md#problem-statement),

```math
\Pr(E_n)=0\quad(n\text{ odd}),\qquad
2^{-n^2/2}\le\Pr(E_n)\le 2^{2n}(n!)^2 2^{-n^2/2}\quad(n\text{ even}).
```

## Proof

For a row cycle of length $`a`$ and a column cycle of length $`b`$, let
$`U,V`$ be the products of the signs on the respective cycles. Multiplying
the symmetry equations over one orbit of cells in the product of the two
cycles gives $`U^{b/g}V^{a/g}=1`$, where $`g=\gcd(a,b)`$. Indeed the orbit
length is $`ab/g`$, so it traverses the row cycle $`b/g`$ times and the
column cycle $`a/g`$ times.

Fix an odd column cycle. The displayed relation then reads $`U=V^a`$
for every row cycle, because $`b/g`$ and $`g`$ are odd. Multiplying over
row cycles gives $`\prod_i u_i=V^n`$. Likewise an odd row cycle with sign
product $`U_0`$ gives $`\prod_j v_j=U_0^n`$. If both permutations have an
odd cycle, the relation for this pair gives $`U_0=V`$ and the total sign
product is positive. For odd $`n`$ each permutation has an odd cycle.
For any $`n`$, at least one permutation of a witness has only even cycles.

Consequently every cell orbit of a possible witness has length at least
two. For fixed permutations and signs, each cell orbit admits at most
two assignments to its entries, since the first sign determines all
others on the orbit. There are at most $`n^2/2`$ orbits. Thus at most
$`2^{n^2/2}`$ out of the $`2^{n^2}`$ sign matrices can realize any
particular witness. The upper bound follows by summing over at most
$`2^{2n}(n!)^2`$ choices.

For even $`n`$, fix a row permutation pairing the rows, take the column
permutation to be the identity, take all row signs to be positive, and
fix a column sign vector with negative product. Choose the first row
of each pair arbitrarily and obtain the second by the fixed column
signs. This gives $`2^{n^2/2}`$ distinct matrices with the same witness,
which proves the lower bound. In particular the base-two logarithm of
$`\Pr(E_n)`$ is $`-n^2/2+O(n\log n)`$ along even orders.
