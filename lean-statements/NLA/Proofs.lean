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
