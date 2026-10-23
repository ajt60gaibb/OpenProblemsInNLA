import NLA.TR06.GraphJacobian

set_option autoImplicit false
noncomputable section
open Set

namespace NLA.Proofs.TR06
open NLA.TR06

/-- The genuine Hilbert product of input tensor and individually normalized
ordered summands. It has the sum-of-squared-norms metric. -/
abbrev NormalizedGraphAmbient (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :=
  WithLp 2 (Tensor ℝ d n × AngularOutput d n r)

def normalizedGraphPoint {d : ℕ} {n : Fin d → ℕ} {r : ℕ}
    (A : Tensor ℝ d n) (a : Fin r → Tensor ℝ d n) : NormalizedGraphAmbient d n r :=
  WithLp.toLp 2 (A, normalizedTuple a)

/-- An open annulus larger than the closed-open annulus used in the Gaussian
estimate. Openness permits genuine smooth manifold charts at both of the
smaller annulus's boundaries. All ordered decomposition branches are retained. -/
def normalizedAnnularGraph (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :
    Set (NormalizedGraphAmbient d n r) :=
  {z | z.ofLp.1 ∈ smoothRegularSet d n r ∧
    (1 / 2 : ℝ) < ‖z.ofLp.1‖ ∧ ‖z.ofLp.1‖ < 3 ∧
    ∃ a : Fin r → Tensor ℝ d n,
      Decomposes a z.ofLp.1 ∧ z.ofLp.2 = normalizedTuple a}

end NLA.Proofs.TR06
