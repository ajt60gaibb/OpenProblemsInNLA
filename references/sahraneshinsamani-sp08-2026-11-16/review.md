# SP-08 integration review, 19 November 2026

Reviewer is the independent Codex AI agent integrating PR #386, separate from
mathematical author Nima Sahraneshinsamani. This is an informal mathematical
and certificate review. The accepted scope is the dimension-eight result
for every real parameter in $`[-1,1)`$, with SP-08 remaining Partially resolved.
The source revision is `cf035d2d7ff9db0b0a16471891fe413bd59281ef`.
[Reviewed source package](https://github.com/snima/sp08-dimension-eight/tree/cf035d2d7ff9db0b0a16471891fe413bd59281ef).

The reviewed argument uses the signed-threshold reduction in Section 2,
the elementary left-strip lemma and the prior Holden strip, and the remainder,
tied-family, near-one and complete dimension-eight arguments in Section 5.
The density argument preserves orthonormality and handles both components
when the dimension is two. At each of the 16 rational nodes, exact bounds
cover all 32,754 candidates outside the two-block family. Convexity bounds
their envelope by the chord, while the tangent bounds the two-block spread
from below. The 15 contiguous intervals meet the left strip at $`-97/100`$
and the near-one interval at $`499/500`$. Both cluster-switch parameters
$`-5/7`$ and $`1/5`$ are nodes.

The elementary left-strip lemma labels its two listed classes exhaustive,
but does not explicitly list the constant-sign sequences with one run.
For those, $`S=\pm dd^T`$ and $`A=\mu J_8+\rho S`$, where
$`\mu=(1+a)/2`$ and $`\rho=(1-a)/2`$. Spread subadditivity gives
$`s(A)\le8\mu+8\rho=8`$, strictly below
$`s(B_{8,4}(a))=8\sqrt{1+\rho^2}`$ on the strip. This supplies the omitted
case. Independently, the already reviewed Holden strip contains
$`-97/100`$ because $`64(1-97/100)=48/25<1+\sqrt2`$.

The near-one remainder follows from the two block-secular eigenvalue
bounds. The exact integer enumeration separates 32,765 patterns with
first-order coefficient below $`963/1000`$ from three ties. Two ties are
two-block patterns, and the third has $`H=J_2\oplus0_4\oplus J_2`$.
The latter is excluded by the exact identity that the squared-spread
difference is $`(X-Y)^2/4>0`$. Its spread difference has leading term
$`(1-a)^2/16`$ as $`a\to1^-`$. The published formula is an asymptotic
expansion, and the strict algebraic identity supplies the interval proof.

The following commands were rerun against these source bytes with Python
3.13.14 and NumPy 2.5.5 for the node audit.

```sh
python3 -B -O check_n8_standalone.py
python3 -B sp08_independent_psd_audit.py all
python3 -B -O verify_sp08_n8_near_one.py
```

All exited zero. The node audit checked 32,754 non-two-block patterns at
each of 16 nodes, with upper and lower integer positive-definiteness tests,
for 1,048,128 tests. All 30 rational chord-tangent inequalities passed.
Floating-point eigenvalues in the node audit propose rational bounds whose
acceptance is checked by integer elimination. The standalone rational checker
checks the interpolation inequalities from the JSON bounds. The separate
node audit establishes those bounds. The near-one checker visited all
32,768 patterns and reported the three expected ties, with integer
arithmetic throughout. These reruns cover the integer node bounds, rational interpolation, and
near-one enumeration.

The sign-run decomposition and all-runs deficit in Sections 2 and 4 concern
signed-threshold sign matrices. The wider uniform left strip is stated for
$`n\ge7`$. The catalog records these scopes. The original all-dimensions
target continues beyond dimension eight and the established boundary strips.

| Reviewed file | SHA-256 |
| --- | --- |
| `paper.tex` | `2333b5ce99957b105e63b38363e38a80a43396d1430fc41053809dbb15c11402` |
| `n8_certified_data.json` | `8930b94513d27e7bdc96c9d1e90dc7951c67767ed4fefa197a72f202017bf7ca` |
| `check_n8_standalone.py` | `62e0ea490c69910cc7e16be502ae5db53c16df4fc35ad5abbbf6652bb50c7545` |
| `sp08_independent_psd_audit.py` | `cdacaa671bff7a89773f9127ac05294d3b6329ef9a250d0a9091f2aaf2b4d3e6` |
| `verify_sp08_n8_near_one.py` | `34865256ba821ae0df8c6a8ebf0ecd72bd1c18c8e83a6b10d34c6908ae17a35d` |
| `verify_sp08.py` | `6ba0672e7c0afd1a5cf587f49ae5f009c0e7031260643983300cbd37bdad3444` |
| `verify_sp08_intervals.py` | `12bf64055b8d667c16378b18d650819cbeff7e574629d0d08b65431732ca6a5f` |
