# Exact finite-order sign discrepancy

Let $`D_n=\sqrt n\,d_n`$ be the largest discrepancy of a square sign
matrix of order $`n`$ from [MD-05](README.md). The values below refer
to the finite order in their own column.

| $`n`$ | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 13 | 14 | 16 | 17 | 19 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| $`D_n`$ | 1 | 2 | 1 | 2 | 3 | 4 | 3 | 4 | 5 | 4 | 5 | 5 | 6 | 6 | 7 | 7 |

## Upper bounds

Identify a sign vector with the binary mask of its negative
coordinates. The inner product between row mask $`r`$ and signing
mask $`x`$ is $`n-2\,\mathrm{popcount}(r\mathbin{\oplus}x)`$.
For an integer $`b>0`$ of parity $`n`$, its absolute value is at least
$`b`$ exactly when $`x`$ belongs to one of the Hamming balls of radius
$`(n-b)/2`$ centered at the row and its complement. Thus discrepancy
at least $`b`$ requires a covering code with at most $`2n`$ codewords
at this radius. Comparing the sum of ball sizes to $`2^n`$ proves all
the upper bounds in the table except at $`n=10,13,16,19`$.

At these four orders use the binary covering-number lower bounds
$`K(10,2)\ge23`$, $`K(13,3)\ge28`$, $`K(16,4)\ge33`$, and
$`K(19,5)\ge40`$. Each exceeds $`2n`$ for the corresponding order.
These bounds are in Table I of [Li and Chen, *New Lower Bounds for
Binary Covering Codes*](https://doi.org/10.1109/18.335963)
([full paper](https://www.academia.edu/5121696/New_lower_bounds_for_binary_covering_codes)).
In all cases parity reduces the asserted upper bound to excluding
discrepancy two larger than the tabulated value.

## Witnesses and finite verification

The masks for orders 6, 9 and 17 are the Griego, Xie and Youhua Li
witnesses in the [Optimization Constants collection](https://teorth.github.io/optimizationproblems/constants/10c.html).
The same masks give witnesses at other orders by using positive signs
in additional columns and padding the row list by repetitions. The order-14
mask list was found by a search for an antipodal cover. The code checks
all the displayed witnesses and the binomial count in exact integers.
It includes the four cited covering-number bounds as inputs.

```python
from math import comb


def walsh(order):
    return tuple(
        sum(((i & j).bit_count() % 2) << j for j in range(order))
        for i in range(order)
    )


rows6 = (0, 7, 9, 21, 12, 26)
rows9 = (0, 7, 25, 30, 42, 45, 51, 52)
rows14 = (
    0, 4002, 1516, 3359, 4282, 6343, 6701,
    5962, 2776, 6037, 1655, 7536, 887, 1513,
)
rows17 = (
    0x0, 0x7F, 0x787, 0xBB8, 0x15D9, 0x1ACE, 0x1D62, 0x1E35,
    0x26F2, 0x29E5, 0x2D1E, 0x2E49, 0x332B, 0x3354, 0x34AC, 0x3893,
)
orders = {
    1: (1, (0,)),
    2: (2, walsh(2)),
    3: (1, (0,)),
    4: (2, walsh(4)),
    5: (3, (0, 1, 2, 3, 4)),
    6: (4, rows6),
    7: (3, rows6),
    8: (4, walsh(8)),
    9: (5, rows9),
    10: (4, rows9),
    11: (5, rows9),
    13: (5, rows9),
    14: (6, rows14),
    16: (6, rows17),
    17: (7, rows17),
    19: (7, rows17),
}
covering_lower_bounds = {(10, 2): 23, (13, 3): 28, (16, 4): 33, (19, 5): 40}

for n, (target, rows) in orders.items():
    assert 0 < len(rows) <= n and all(0 <= row < 1 << n for row in rows)
    # Complementing a signing preserves all absolute row sums.
    discrepancy = min(
        max(abs(n - 2 * (x ^ row).bit_count()) for row in rows)
        for x in range(1 << (n - 1))
    )
    assert discrepancy == target, n
    radius = (n - target - 2) // 2
    ball_count = 2 * n * sum(comb(n, j) for j in range(radius + 1))
    assert ball_count < 1 << n or covering_lower_bounds.get((n, radius), 0) > 2 * n, n
```
