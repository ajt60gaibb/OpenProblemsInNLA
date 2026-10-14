# TR-14 affine chart polynomial: independent final review

**Disposition:** approve the exact polynomial identity for aggregate import as a partial chart gate. Projective-root multiplicity preservation, arbitrary ordinary-width lower bound, and the full TR-14 Target remain open.

I independently inspected `GL2AffineChartPolynomial.lean` at SHA-256 `b0ec8b4adc5fc3afb79baf0e7fc462079e86cdd987f88ff0e979f3d05a5bee85` against the unchanged canonical TR-14 source, frozen Target, and [independently reviewed precontract](GL2_AFFINE_CHART_POLYNOMIAL_INDEPENDENT_PRE_REVIEW.md). The public theorem quantifies over every `d,z,g`, including `d=0`, `z=0`, the zero vector, and trailing zeros, and asserts the exact equality in `Polynomial ℂ`:

`dehomogenize d (transportedApolarVector z d g) = Σᵢ C(gᵢ) X^(d−i) (1+C(z)X)^i`.

The proof evaluates both polynomials at arbitrary `t`. The left is evaluation of the actual transported homogeneous form at `(1,t)`; the audited `chartPhi` substitutes `(X,Y)↦(Y,X+zY)`, so this equals evaluation of the original form at `(t,1+zt)`. Expanding the audited monomial basis `X^(d−i)Y^i` gives the right-hand sum, and polynomial evaluation extensionality closes the equality. No apolarity, root multiplicity, genericity, or coefficient reversal beyond `d−i` enters. At `d=2`, the result is `c+(b+2cz)t+(a+bz+cz²)t²` for `g=(a,b,c)`; at `z=0` it is exact reversal, and its leading coefficient is the previously audited `G(1,z)`.

The author passed pinned Lean 4.33.1 direct and module builds in LeanCert `kernel` mode (3,036 module jobs). My separate imported exact-signature audit `/private/tmp/tr14-affine-chart-polynomial-independent-audit.lean` at SHA-256 `837ef5aca6b1fb526f58223960fa254083f625427cfd6e33420c8fe5a54dbc26` passed `#assert_trust kernel`; `#print axioms` lists only `propext`, `Classical.choice`, and `Quot.sound`. A banned-placeholder scan found no `sorry`, `admit`, `native_decide`, `unsafe`, or custom axiom.
