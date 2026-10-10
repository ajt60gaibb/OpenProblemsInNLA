import NLA.Proofs.RA06.GraphSupportCount
import NLA.Proofs.RA06.GraphSampling
import NLA.Proofs.RA06.Bernoulli
import NLA.Proofs.RA06.GraphFinite
import NLA.Proofs.RA06.Asymptotic
import NLA.Proofs.RA06.Final
import NLA.Proofs.MF03.OrderOne
import NLA.Proofs.MF03.Transport
import NLA.Proofs.MF03.Finite02
import NLA.Proofs.MF03.Finite03
import NLA.Proofs.MF03.Finite04
import NLA.Proofs.MF03.Finite05
import NLA.Proofs.MF03.Finite06
import NLA.Proofs.MF03.Finite07
import NLA.Proofs.MF03.Finite08
import NLA.Proofs.MF03.Finite09
import NLA.Proofs.MF03.Finite10
import NLA.Proofs.MF03.Finite11
import NLA.Proofs.MF03.Finite12
import NLA.Proofs.MF03.Finite13
import NLA.Proofs.MF03.Finite14
import NLA.Proofs.MF03.Finite15
import NLA.Proofs.MF03.FiniteRange
import NLA.Proofs.MF03.CosineTail
import NLA.Proofs.MF03.WaveAtThree
import NLA.Proofs.MF03.CosineProduct
import NLA.Proofs.SP14.SubsequenceGap
import NLA.Proofs.SP14.BaseCoefficient
import NLA.Proofs.SP14.BaseBlockCharpoly
import NLA.Proofs.SP14.BaseProductBlock
import NLA.Proofs.SP14.BaseCB
import NLA.Proofs.SP14.BaseFourierMode
import NLA.Proofs.SP14.BaseParityIndex
import NLA.Proofs.SP14.BaseParityBlocks
import NLA.Proofs.SP14.BaseOffdiagonalCharpoly
import NLA.Proofs.SP14.BaseToeplitzCharpolyConditional
import NLA.Proofs.SP14.BaseCoeffSummable
import NLA.Proofs.SP14.BaseExteriorSeries
import NLA.Proofs.SP14.BaseExteriorFourier
import NLA.Proofs.SP14.BaseExteriorPattern
import NLA.Proofs.SP14.BaseExteriorBoundarySquare
import NLA.Proofs.SP14.PositivePacketInvisibility
import NLA.Proofs.SP14.NegativeRestorationInvisibility
import NLA.Proofs.SP14.OddFrequencyToeplitzCharpoly
import NLA.Proofs.SP14.FiniteCorrectedOddSupport
import NLA.Proofs.SP14.JetVanishingMultiplicity
import NLA.Proofs.SP14.BaseJetTriangular
import NLA.Proofs.SP14.BaseJetCorner
import NLA.Proofs.SP14.BaseJetFourierMatrix
import NLA.Proofs.SP14.BaseJetPencilFormula
import NLA.Proofs.SP14.BaseJetRealSolve
import NLA.Proofs.SP14.SobolevOversampling
import NLA.Proofs.SP14.WeightedSobolevPhysical
import NLA.Proofs.SP14.WeightedSobolevOperators
import NLA.Proofs.TR14.WidthBasics
import NLA.Proofs.TR14.MomentIndex
import NLA.Proofs.TR14.ApolarMinimal
import NLA.Proofs.TR14.NormalizedQuotient
import NLA.Proofs.TR14.FrobeniusMinimal
import NLA.Proofs.TR14.MiddleCatalecticant
import NLA.Proofs.TR14.GL2Homogeneous
import NLA.Proofs.TR14.GL2CoefficientBasis
import NLA.Proofs.TR14.GL2MomentDual
import NLA.Proofs.TR14.GL2ApolarPairing
import NLA.Proofs.TR14.GL2ApolarTransport
import NLA.Proofs.TR14.GL2Dehomogenize
import NLA.Proofs.TR14.GL2ChartNormalize

/-!
Build and kernel-audit the reviewed RA-06 theorem inhabiting the frozen
original target. Compile the separately scoped MF-03 order-one-through-fifteen
target clauses, analytic tail and value-at-three bounds, and initial product
convergence. Compile the conditional SP-14 subsequence, finite base-block
algebra, frozen integral's pure-mode Fourier orthogonality, and the conditional
actual Toeplitz odd-order characteristic polynomial. These are not full-target
proofs. The exterior half-binomial coefficient norms are summable, and the
normalized exterior boundary series is continuous and has a justified
all-integer Fourier-coefficient series under the frozen interval integral.
The exterior base symbol's all-integer Fourier pattern and actual odd Toeplitz
characteristic polynomial are unconditional; they are not the SP-14 target.
The normalized base symbol also satisfies its square identity and boundary
zero criterion at every circle point.
The first positive packet has exact frozen Fourier support and preserves
smaller Toeplitz sections over continuous backgrounds.
The finite negative restoration packet cancels at the endpoint, its restoring
term is invisible at its matching section, and the full packet preserves
earlier sections under the source's numerical separation hypotheses.
Under exact vanishing of the frozen even Fourier coefficients, every odd
Toeplitz section has an explicit characteristic-polynomial quotient in the
source's jet coordinate.
Every finite corrected symbol made from the exterior base and source packets
is continuous, has this exact odd Fourier support, and inherits that shape.
If its first jet coefficients vanish, the actual characteristic-root multiset
has the corresponding algebraic multiplicity at both `1` and `-1`.
The source's explicit real base-jet matrix has a verified triangular inverse;
its identification with the actual Toeplitz jet map is still outstanding.
The selected finite block's characteristic polynomial equals an exact pencil
adjugate corner for arbitrary block data, including the empty lower block.
For the exterior base plus one restored negative packet, the actual frozen
Fourier coefficients seen by the selected section equal the coefficient-defined
upper triangular matrix; both odd Toeplitz blocks have the required orientation.
The corrected section's actual odd jet polynomial obeys the source's exact
finite triangular pencil formula for every allowed order and packet size.
The resulting real first-jet map equals the source triangular matrix, has an
explicit right inverse, and has bijective derivative at every base-model vector.
The source's Sobolev oversampling operator algebra has its exact five conclusions
from explicit compatible inverse and weighted projection estimates.
The complete complex `ℓ²` carrier has an exact coefficientwise bijection to
physical Sobolev sequences with finite `(n+1)^(2s)` energy and its norm-square
identity. Continuous inclusion, truncation, and finite lift preserve literal
physical coefficients, and their sharp `q+1` tail and `h` band estimates hold.
Background-dependent compatible inverse bounds remain separate obligations.
TR-14 width semantics supply the symmetric-to-ordinary direction and exact
zero-width endpoints. Every moment coordinate appears in the frozen Hankel
tensor; the exact apolar map has a least nonzero degree for nonzero moments.
Under a monic affine apolar premise, the normalized quotient functional matches
every moment through the full tensor degree.
With the exact least-apolar-degree premise, that quotient functional also has
the full Frobenius nondegeneracy property, by the power-basis argument.
In the same normalized monic chart, the exact middle Hankel catalecticant
has rank equal to the least apolar degree, including balanced and odd cases.
An explicit homogeneous binary-form chart is invertible in every degree,
respects multiplication, and has the exact inverse-dual moment pairing.
The complete zero-based monomial basis identifies every coefficient vector
with a genuine homogeneous form, and multiplication adds the indices exactly.
The unweighted homogeneous moment dual has exact monomial coordinates,
inverse coordinate reconstruction, and the inverse-dual chart relation.
Every frozen apolar equation is equivalent to annihilation of all
complementary homogeneous products, including every endpoint degree.
The inverse-dual chart carries every degree's apolar kernel to its exact
image and preserves existence of nonzero apolar forms in every degree.
For every nonzero homogeneous coefficient vector, exact affine
dehomogenization and the explicit chart yield a nonzero transformed final
coefficient, including degree zero and an initial infinity root.
Any chosen nonzero least apolar vector can therefore be transported and
scaled to a monic affine polynomial of exact least degree, while all lower
apolar kernels remain zero in the chosen chart.
These results do not prove the full all-width rank equality.
-/

set_option leancert.trust "kernel"

#assert_trust kernel NLA.Proofs.RA06.graphMatrix_fullColumnRank
#assert_trust kernel NLA.Proofs.RA06.graphMatrix_inputEnergy
#assert_trust kernel NLA.Proofs.RA06.graphMatrix_totalSensitivity_bound
#assert_trust kernel NLA.Proofs.RA06.embedding_to_weighted
#assert_trust kernel NLA.Proofs.RA06.sample_positiveEdgeCount_eq_retainedCount
#assert_trust kernel NLA.Proofs.RA06.positiveEdgeCount_lower_of_all_degrees
#assert_trust kernel NLA.Proofs.RA06.expectedSize_eq_sum_count
#assert_trust kernel NLA.Proofs.RA06.expectedSize_lower_of_success_count_bound
#assert_trust kernel NLA.Proofs.RA06.supportDegree_lower_of_approx
#assert_trust kernel NLA.Proofs.RA06.successful_retainedCount_lower
#assert_trust kernel NLA.Proofs.RA06.expectedSize_lower_from_graph_success
#assert_trust kernel NLA.Proofs.RA06.exists_large_accuracy_parameter_for_coefficients
#assert_trust kernel NLA.Proofs.RA06.finite_bounds_contradict_for_coefficients
#assert_trust kernel NLA.Proofs.RA06.budget_log_upper_for_ceiling_card_bound
#assert_trust kernel NLA.Proofs.RA06.target
