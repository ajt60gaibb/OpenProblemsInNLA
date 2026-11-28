# Conditioning the Paley frame on progression supports

Let $`p\equiv1\pmod4`$ be prime, let $`\chi`$ be its quadratic character
with $`\chi(0)=0`$, and use the Paley frame $`\Phi_p`$ from
[FR-03](README.md). Suppose the finite column labels $`S_0`$ of $`S`$
are contained in the union of $`r`$ progressions

```math
P_j=\{a_j+d\ell\bmod p:0\le\ell<H_j\},
\qquad 1\le j\le r,\quad d\ne 0,\quad H_j\le H.
```

Fix $`0<\eta<1/16`$ and $`r`$. If $`H\le p^{9/16-\eta}`$, then for
all sufficiently large $`p`$,

```math
\big\|(\Phi_p)_S^*(\Phi_p)_S-I\big\|_2
\le C_\eta r\,p^{-\eta/3} + \sqrt{|S_0|/p}.
```

The final term can be omitted when $`S=S_0`$.

## Proof

The quadratic Gauss sum gives $`\langle \phi_x,\phi_y\rangle =
p^{-1/2}\chi(x-y)`$ for distinct finite labels. The diagonal is one.
Since $`\chi(0)=0`$ the finite-column Gram deviation is therefore
$`p^{-1/2}(\chi(x-y))_{x,y\in S_0}`$.

Assign each point of $`S_0`$ to one progression containing it. This
partitions the Gram deviation into at most $`r^2`$ blocks. Before
restricting to the columns and rows assigned to $`P_j`$ and $`P_i`$,
respectively, the unscaled block is the rectangular matrix on the two
integer index intervals with entries

```math
\chi(a_i-a_j+d(\ell-\ell'))
  =\chi(d)\chi(c_{ij}+\ell-\ell'),
\qquad c_{ij}=d^{-1}(a_i-a_j)\pmod p.
```

It is a submatrix of the convolution on $`\ell^2(\mathbb Z)`$ with
coefficients $`\chi(d)\chi(c_{ij}+h)`$ for
$`-(H_j-1)\le h\le H_i-1`$ and zero elsewhere. The Fourier transform
diagonalizes this convolution. It follows that the block and all its
restrictions have operator norm at most

```math
\sup_{\theta\in\mathbb R}
\left|\sum_{h=-(H_j-1)}^{H_i-1}
              \chi(c_{ij}+h)e^{2\pi\mathrm i h\theta}\right|.
```

This is a linear-phase mixed character sum on one interval, after
shifting by an integer representative of $`c_{ij}`$. Theorem 1.4 of
[Heath-Brown and Pierce](https://arxiv.org/pdf/1404.1677), with moment
parameter three and loss $`p^{\eta/3}`$, bounds it by
$`C_\eta (2H)^{2/3}p^{1/8+\eta/3}`$. The interval length is below
the theorem's limit $`p^{5/8}`$ for sufficiently large $`p`$.
Dividing by $`\sqrt p`$ gives $`O_\eta(p^{-\eta/3})`$ per block.
If each block has norm at most $`b`$, the vector of norms of the block
outputs is bounded coordinatewise by $`b`$ times the sum of norms of the
input blocks. Cauchy–Schwarz then bounds the total operator norm by
$`rb`$.

The infinity column has inner product $`p^{-1/2}`$ with every finite
column. Its additional off-diagonal row and column form a Hermitian
matrix of norm $`\sqrt{|S_0|/p}`$. This proves the displayed estimate.
For fixed $`\eta,r`$ both terms vanish. If the Gram deviation is at
most $`\delta<1`$, then the squared singular values are in
$`[1-\delta,1+\delta]`$ and the condition number is at most
$`\sqrt{(1+\delta)/(1-\delta)}`$.
