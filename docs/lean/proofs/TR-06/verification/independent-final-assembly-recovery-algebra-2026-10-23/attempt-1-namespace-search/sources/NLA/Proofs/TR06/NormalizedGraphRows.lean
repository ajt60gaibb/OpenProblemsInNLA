import NLA.Proofs.TR06.NormalizedGraphEuclidean
import NLA.Proofs.TR06.NormalizedGraphAlgebra

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR06
open NLA.TR06 NLA.TR06.Area.Proposed GraphAlgebra

/-- Reassemble literal input/output coordinates into the actual Hilbert product.
This map only changes the finite coordinate representation. -/
def graphCoordinateDecode {d : ℕ} {n : Fin d → ℕ} {r : ℕ} :
    (OutputCoordinate d n r → ℝ) →ₗ[ℝ] NormalizedGraphAmbient d n r where
  toFun x := WithLp.toLp 2
    ((WithLp.toLp 2 (fun q : TensorIndex d n => x (.inl q)) : Tensor ℝ d n),
     (WithLp.toLp 2 (fun iq : Fin r × TensorIndex d n => x (.inr iq)) : AngularOutput d n r))
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def graphCoordinateEncode {d : ℕ} {n : Fin d → ℕ} {r : ℕ}
    (z : NormalizedGraphAmbient d n r) : OutputCoordinate d n r → ℝ :=
  Sum.elim (fun q => z.ofLp.1 q) (fun iq => z.ofLp.2 iq)

@[simp] theorem graphCoordinateDecode_encode {d : ℕ} {n : Fin d → ℕ} {r : ℕ}
    (z : NormalizedGraphAmbient d n r) : graphCoordinateDecode (graphCoordinateEncode z) = z := rfl

/-- Fixed real rows describing a selected Euclidean coordinate projection of
actual graph input/output coordinates. Arbitrary orthonormal bases are allowed. -/
def graphProjectionRows {d : ℕ} {n : Fin d → ℕ} {r k : ℕ}
    (σ : Fin k ↪ Fin (graphAmbientDimension d n r)) : Fin k → OutputCoordinate d n r → ℝ :=
  fun j c => coordProjection σ (graphEuclideanEquiv d n r
    (graphCoordinateDecode (fun b => if c=b then 1 else 0))) j

theorem graphProjectionRows_apply {d : ℕ} {n : Fin d → ℕ} {r k : ℕ}
    (σ : Fin k ↪ Fin (graphAmbientDimension d n r)) (x : OutputCoordinate d n r → ℝ)
    (j : Fin k) :
    ∑ c, graphProjectionRows σ j c * x c =
      coordProjection σ (graphEuclideanEquiv d n r (graphCoordinateDecode x)) j := by
  let L := (coordProjectionL σ).toLinearMap.comp
    ((graphEuclideanEquiv d n r).toLinearEquiv.toLinearMap.comp
      (graphCoordinateDecode (d := d) (n := n) (r := r)))
  have H := LinearMap.pi_apply_eq_sum_univ L x
  change coordProjection σ (graphEuclideanEquiv d n r (graphCoordinateDecode x)) =
    ∑ c, x c • coordProjection σ (graphEuclideanEquiv d n r
      (graphCoordinateDecode (fun b => if c=b then 1 else 0))) at H
  have h := congrArg (fun z : Euclid k => z j) H
  simpa only [WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,
    graphProjectionRows,mul_comm] using h.symm

#assert_trust kernel graphProjectionRows_apply
#print axioms graphProjectionRows_apply
end NLA.Proofs.TR06
