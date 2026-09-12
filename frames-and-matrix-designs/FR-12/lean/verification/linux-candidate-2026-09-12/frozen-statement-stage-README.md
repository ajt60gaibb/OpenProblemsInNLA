# FR-12 Lean statement package

The complete labeled real Hadamard counting conjecture and seven supporting
statements are being formalized. This package currently contains definitions
and an intentionally incomplete Challenge, not a completed proof. Two
independent statement approvals are required before implementation. The
canonical problem remains Solved, with its existing informal proof.

**Mathematical proof and formalization:** George Stepaniants, Department of
Computing and Mathematical Sciences, California Institute of Technology,
Pasadena, California, USA. Substantial AI-agent assistance is disclosed.
Ferber, Jain and Zhao retain the original conjecture and upper-bound credit.

Read [NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md) for the complete obligations,
the exact smaller injection, endpoint conventions, and excluded stronger
claims. [SOURCE_MAP.md](SOURCE_MAP.md) records correspondence and provenance.

The construction uses a permutation to match the first block of row labels to
the second. Its m! factor suffices for the exact source lower bound, avoiding
all-perfect-matching enumeration. All counts still refer to individual labeled
real matrices; no quotient or change of the original target is made.

The project pins Lean 4.33.1, LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`, and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. At this stage run:

```sh
lake build NLA.FR12.Definitions Challenge
```

The seven Challenge placeholder warnings are intentional and establish no
theorems. A completed Solution must never import Challenge. Later verification
must use LeanCert kernel trust checks, only the three allowed axioms, and actual
Linux Comparator/default-kernel replay. No interval search is mathematically
needed for the current exact construction.

The structure follows the campaign's shared audited infrastructure and the
pinned Forsythe example. Schiffer was studied for organization; no Schiffer
proof code is copied. Independent AI referees are not external human peer
review, Tau Ceti endorsement, or an attribution of the proof to those projects.
