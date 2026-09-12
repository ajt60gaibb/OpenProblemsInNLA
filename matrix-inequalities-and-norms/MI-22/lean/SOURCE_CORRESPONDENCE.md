# MI-22 source correspondence and exact adaptation

The immutable source base is
`8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc` of
`ajt60gaibb/OpenProblemsInNLA`. The full canonical statement, complete exported
TeX proof and submission note, and complete retained informal review were read.
`reviews/source-hashes.json` binds eight original files and confirms that every
one matches its base Git blob. The source PDFs are retained unchanged; this
statement preparation does not claim a new visual PDF inspection.

## Original target and conventions

The [retained canonical page](../README.md) asks for the singular-value
log-majorization of `A^t(A#_tB)B^(1-t)` by `AB`, over every positive dimension,
every complex positive definite pair, and every real `t∈[0,1]`. The complete
proper-prefix inequalities and equality at the full dimension are preserved in
`SingularLogMajorized` and `WeightedLogMajorizationConjecture`.

The primary preprint defines singular values as the decreasing eigenvalues of
the positive modulus, defines the weighted mean using the same noncommuting
order of factors, distinguishes log-majorization from its weak version, and
states the weighted singular-value target as Conjecture 1.1. Its broader
semidefinite formulation contains the canonical positive-definite case. The
neighboring Conjecture 1.2 and eigenvalue-modulus results are separate targets.
These conventions were checked on printed pages 1–3, without claiming a new
literature or priority survey. [Ghabries–Abbas–Mourad–Assi primary preprint](https://arxiv.org/pdf/2105.13356).

## Source proof and changed witness

The original negative resolution and printed witness are Matthew J. Colbrook's,
Department of Applied Mathematics and Theoretical Physics, University of
Cambridge. The complete proof is [solution.tex](../solution.tex), Theorem 1.1
and its proof. Its normalized original TeX SHA256 is
`4c7c612af0a3f285c1d373d16847450d7fb99582fd2906eec8202c2a8ea9c5a4`.

The source uses `A=diag(256,1/256,1)` and an integer matrix B. It supplies
rational approximations R to `(A^(-1/2) B A^(-1/2))^(1/8)` and S to `B^(1/8)`,
then proves residual-to-root and product-error bounds. The source's reported
norm thresholds are 10900 and 10200.

**This candidate uses an adapted rational B and different thresholds.** It does
not assert that the original printed B equals the candidate's B or that the
source contains this adapted displayed matrix. The adaptation and formalization
were prepared for George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, Pasadena, California, USA, with
AI assistance. The mathematical strategy and original negative resolution remain
attributed to Colbrook; no new historical-priority claim is made.

Specifically, D is the source's positive square root of A. T is obtained by
rounding each exact rational entry of the source's R to the nearest multiple of
`1/8192`. The candidate then **defines** `B=D T^8 D` exactly. The source's
integer B and its approximation S are not used in this witness. The reconstruction
script parses R directly from the complete source TeX and verifies the stated
rounding provenance with exact fractions. This records selection of a rational
candidate, not an approximate premise of the proof.

After proving T positive definite, actual CFC makes the root of `D⁻¹ B D⁻¹=T^8`
equal T exactly. The other root `Y=B^(1/8)` remains an actual principal root.
The identity `L Y=N`, the trace bound `‖Y‖₂<4`, and one exact Euclidean unit
test vector provide the strict gap `‖AB‖₂<10500<11000<‖L‖₂`. Thus no approximate
matrix root or source Lipschitz lemma is needed. This changes the counterexample
data and proof route while retaining the complete original target.

## Correspondence of every statement

| Formal object or export | Source meaning and additional obligation |
| --- | --- |
| `spectralPower`, `spectral_power_semantics` | Actual principal powers; the generic theorem gives their unitary spectral representation for every positive definite complex input and real exponent. |
| `weightedMean`, `leftProduct` | Exact original weighted mean and product, preserving the noncommuting factor order. |
| `singularValue`, `singular_values_semantics` | Actual Mathlib singular values of the Euclidean linear map, retaining all sorted eigenvalue multiplicities; zero-based first index is the source's `s₁`. The first-value/operator-norm bridge is required. |
| `singularPrefix`, `SingularLogMajorized` | Every original prefix product and equality of the complete products. |
| `WeightedLogMajorizationConjecture` | All original dimensions, complex positive definite inputs, and real parameters including endpoints. |
| `operatorNorm`, `frobeniusSquared`, `euclidean_norm_bounds` | Actual induced Euclidean norm, sum of all squared complex moduli, and their generic action/comparison bridges. |
| `witnessA`, `witnessT`, `witnessB` | A is unchanged; T is the documented exact dyadic adaptation; B is newly defined by exact congruence. |
| `witness_rational_data` | Proves every finite LDL, positivity, unit-vector, trace, tested coordinate and Frobenius bound for the adapted data. |
| `witness_principal_powers` | Proves all actual CFC identities, positivity of the true remaining root, original-order reduction `L Y=N`, and its norm bound. |
| `witness_operator_gap` | Strict estimates for the actual original products at the adapted witness. |
| `counterexample` | Full original admissibility and actual first-singular-value reversal, hence failure of full log-majorization. |
| `not_weightedLogMajorizationConjecture` | Negation of the entire canonical universal statement. |

The source's root-approximation error theorem, residual inequalities, particular
integer B, and exact thresholds 10900/10200 are deliberately not advertised as
formalized. They are unnecessary to the adapted full-target counterexample.
The adaptation does not classify the valid parameter ranges or assert failure
at every t. There is no added commutation, rank, positivity-of-certificate, or
root-existence hypothesis in the canonical target.

## Library reuse and reproducibility

The package pins Lean 4.33.1, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`. The formalization reuses actual Mathlib
Euclidean matrix maps, singular values, positive-definite matrices, CFC powers,
and exact rational arithmetic. The API and project organization follow the
reviewed neighboring MI/RA projects, particularly RA-03's actual singular-value
definition, the MI-21/MI-29 CFC interfaces, and the matrix norm/trace techniques
used for MI-23. No unverified neighboring theorem is imported as an assumption.

The standard-library Fraction script in `reviews/reconstruct.py` independently
recomputes the finite data without importing the original submission's verifier.
It is the statement author's diagnostic, not a second-agent review or a formal
certificate. Its JSON output contains every exact rational value. The planned
proof uses repeated squaring, exact LDL and matrix multiplication, a genuine
norm bridge, and one retained kernel LeanCert scalar comparison. It uses no
floating-point spectral result, interval partition, or numerical root solver.

Both independent statement approvals, two independent final proof reviews,
actual permitted-axiom checks, and the real Linux kernel/Comparator workflow are
required before formal-verification promotion. At this stage only definitions
and intentional Challenge placeholders exist; no completed proof is claimed.

## Original source hashes

| File | SHA256 |
| --- | --- |
| Canonical README | `5e059c072b81dd4e967c8631ee75ad57cca728920340f8a400ff70c32ef0fc63` |
| Canonical problem TeX | `b39e09b44b36ad30d93355d8e1ae4f6025b1341d301cb7ff0f872f3e35737c0e` |
| Canonical problem PDF | `084f6a445a1d9b97eeb3f35215f4d701753554ecbe8a01dd11ebee29d3247ad0` |
| Solution submission note | `cd4119c2689503cf4c772c92c4796db33807731c0624a675e9ab0a21694e5839` |
| Complete exported solution TeX | `a18faf570035b75b334eaf49a3fdfbf72e53b2bcca79869c0306149d0f6877b3` |
| Complete exported solution PDF | `13fc68aa06179114598257b982f8c4a394e7194b622607472c42dac75c964f7c` |
| Original proof TeX | `4c7c612af0a3f285c1d373d16847450d7fb99582fd2906eec8202c2a8ea9c5a4` |
| Original informal review | `dcc87540e4165c49e5ace9a3e836e46d652f19057014ba5d5ab62f994ec34cbf` |
