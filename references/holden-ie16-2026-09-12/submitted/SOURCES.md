# Sources

## 1. Canonical problem statement

Alex Townsend, *Open Problems in Numerical Linear Algebra*, IE-16, “A sharp subset bound for worst-case normal GMRES.”

- [Category supplied in the request](https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/linear-systems-and-elimination)
- [Canonical IE-16 entry](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/linear-systems-and-elimination/IE-16/README.md)
- [Raw statement inspected](https://raw.githubusercontent.com/ajt60gaibb/OpenProblemsInNLA/main/linear-systems-and-elimination/IE-16/README.md)

Accessed 12 September 2026. The inspected entry asks whether the `4/pi` inequality holds for every finite set of distinct nonzero complex points and every `1 <= k <= n-2`, with a constant independent of dimension, degree, and point locations. It lists “Partially resolved” and a last-check date of 10 September 2026, referring to the real-spectrum case. These are statements about the page as inspected, not a claim about later repository updates.

## 2. Original conjecture and interpolation framework

Jörg Liesen and Petr Tichý, *The worst-case GMRES for normal matrices*, **BIT Numerical Mathematics 44** (2004), 79–98.

[Author-hosted full text](https://page.math.tu-berlin.de/~liesen/Publicat/LieTic04.pdf)

The subset formula appears in equation (3.10). The conjecture of a universal constant appears in Section 3.2.2, equation (3.16), page 91. The discussion on page 92 gives `4/pi` as the candidate constant, based on roots-of-unity examples and numerical evidence. The primary paper distinguishes its proved dimension-dependent bound from its conjectured constant bound.

## Attribution and scope

The question and its historical context are attributed to the sources above. The counterexample, detailed arguments, and exact certificate are presented in this package rather than attributed to those sources. The interpolation identities needed in the proof are proved directly in the manuscript. No external paper or repository is reproduced in the archive, and no exhaustive priority claim is made.
