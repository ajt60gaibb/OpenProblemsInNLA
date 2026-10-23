import NLA.Proofs.TR06.NormalizedGraphFiniteVolume
import NLA.Proofs.TR06.NormalizedGraphArea
import NLA.Proofs.TR06.AlgebraicLocusPositiveVolume
import NLA.Proofs.TR06.ModelGaussian
import NLA.Proofs.TR06.ModelMeasureRestoration

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06
open NLA.TR06

/-- The complete unchanged intrinsic target, including the literal
volume-Gaussian law and intrinsic angular derivative condition. -/
theorem target : NLA.Statements.TR06.Target := by
  intro d n r hd hn hr hgeneric
  have hd0 : 0 < d := by omega
  have hn0 : ∀ j, 0 < n j := fun j => by have := hn j; omega
  have hr2 : 2 ≤ r := by omega
  have hgen := (Model.generic_iff (d := d) (n := n) (r := r)).mp hgeneric
  have hfull := AlgebraicLocus.generic_smoothRegular_full_measure hd0 hn0 hr2 hgen
  have hpos := AlgebraicLocus.generic_smooth_annular_volume_pos hd0 hn0 hr2 hgen
  have hfinite := normalizedAnnularGraph_volume_lt_top (n := n) (r := r) hd0
  obtain ⟨hvol,hangular⟩ := NormalizedGraphArea.actualAnnularBounds_of_graphVolume_lt_top hd0 hfinite
  exact Model.finiteAngularMean_of_actualAnnularBounds hd0 (by omega) hfull hpos hvol hangular

#assert_trust kernel target
#print axioms target
end NLA.Proofs.TR06
