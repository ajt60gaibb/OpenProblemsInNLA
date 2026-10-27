import NLA.Proofs.IE22.Assembly
import NLA.Proofs.IE22.UniversalUpper
import NLA.Proofs.IE22.LowerWitness

/-! The literal published IE-22 eventual uniform sharp constant. Both geometric
endpoints are supplied by actual proofs, including all positive row counts in
the upper estimate and arbitrarily large aspect ratios in the sharp witnesses. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.IE22

theorem target : NLA.Statements.IE22.Target := by
  intro θ a hθ0 hθ1 ha hquantile
  exact ⟨uniformUpper_of_squared_bound hθ1.le ha.le
      (uniform_squared_upper θ a hθ0 hθ1 ha hquantile),
    not_uniformUpper_of_squared_witness hθ1.le ha.le
      (near_sharp_unit_row_witness θ a hθ0 hθ1 ha hquantile)⟩

#assert_trust kernel target
#print axioms target
end NLA.Proofs.IE22
