# MI-22 Lean statement candidate

This package states the full Lemos–Soares singular-value log-majorization
conjecture and an exact rational counterexample adapted from Matthew J.
Colbrook's construction. The adapted B is different from the source's printed
integer matrix. The complete original complex positive-definite/all-parameter
target is preserved.

Formalization: **George Stepaniants**, Department of Computing and Mathematical
Sciences, California Institute of Technology, Pasadena, California, USA.
AI-assisted preparation; independent reviews are recorded separately.

The mathematical definitions, numerical targets, and eight Challenge signatures
are prepared before proofs. **No proof implementation is present.** Two
independent statement approvals are required before implementation. Canonical
status remains `Solved`, and no formal-verification promotion is claimed.

- [Numerical and mathematical targets](NUMERICAL_TARGETS.md)
- [Source correspondence and witness adaptation](SOURCE_CORRESPONDENCE.md)
- [Actual definitions](NLA/MI22/Definitions.lean)
- [Statement-only Challenge](Challenge.lean)
- [Exact finite reconstruction](reviews/reconstruct.py)

Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926` are pinned. The intended trust boundary
permits only `propext`, `Classical.choice`, and `Quot.sound`. All final numerical
certificates must select LeanCert kernel mode explicitly.

To check this statement stage:

```sh
lake build NLA.MI22.Definitions Challenge
python3 reviews/reconstruct.py
```

The eight Challenge holes are deliberate and prove nothing. Future Solution
must exclude Challenge. Final proof review and real Linux kernel/Comparator
verification with the repository controls remain later requirements.
