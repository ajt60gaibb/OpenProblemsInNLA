import ProofProject.SourceRadialIntegrability

/-! Angular moments and a fixed sequence approaching the boundary from inside. -/

noncomputable section

namespace ProofProject

def sourceRadius (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ) + 2)

/-- Unnormalized angular moment; normalized circle measure divides by `2π`. -/
def sourceAngularMoment (F : ℂ → ℂ) (k : ℕ) : ℂ :=
  ∫ θ : ℝ in Set.Icc (-Real.pi) Real.pi, F (sourceCircle θ) * sourceCircle θ ^ k

def sourceRadialMoment (F : ℂ → ℂ) (r : ℝ) (k : ℕ) : ℂ :=
  ∫ θ : ℝ in Set.Icc (-Real.pi) Real.pi, F ((r : ℂ) * sourceCircle θ) * sourceCircle θ ^ k

end ProofProject
