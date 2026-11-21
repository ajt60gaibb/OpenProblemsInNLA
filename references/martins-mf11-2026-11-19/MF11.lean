import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Problem MF-11 has a negative answer — a machine-checked proof

This file is a self-contained Lean 4 / Mathlib formalization of the main result of the paper

  *Marginal growth rates of matrix products need not be weakly increasing or regularly varying*
  (Pedro Martins),

namely the negative answer to Problem MF-11 of *Open Problems in Numerical Linear Algebra*
(J. Varney and I. D. Morris, Linear Algebra Appl. 709 (2025), Question 1), given by
Theorem 1.3 of the paper.

## Main statements

* `MF11.MF11_answer_is_no`: Problem MF-11 **exactly as posed** has a negative answer. It is not
  true that every compact nonempty set `𝓜` of real square matrices with joint spectral radius
  `lim_k g_𝓜(k)^{1/k} = 1` has a maximal product norm sequence
  `g_𝓜(k) = max {‖A_k ⋯ A_1‖₂ : A_i ∈ 𝓜}` (spectral norm `‖·‖₂`, as in the problem) that is
  both weakly increasing and weakly upper regularly varying.
* `MF11.MF11_negative_answer_spectral`: the counterexample. For the two real `20 × 20` matrices
  `F20 false = F₀(θ⋆)` and `F20 true = F₁(θ⋆)` of Theorem 1.3 and the spectral norm, the
  sequence `g(k) = max {‖F_{b₁} ⋯ F_{b_k}‖₂ : b ∈ {0,1}^k}` satisfies
  - `g(k)^{1/k} → 1`, i.e. the joint spectral radius of the pair is `1`;
  - `k/20 ≤ g(k) ≤ 800 k³`;
  - `¬ WeaklyIncreasing g`  (there is no `c > 0` with `g(k+ℓ) ≥ c g(k)` for all `k, ℓ ≥ 1`);
  - `¬ WeaklyUpperRegularlyVarying g`  (it is false that for every `ℓ ≥ 1` there is
    `C_ℓ > 0` with `g(ℓk) ≤ C_ℓ g(k)` for all `k ≥ 1`).
* `MF11.MF11_negative_answer`: the same for **every** norm on `20 × 20` matrices (precisely: for
  every `nrm` with `c · rowNorm ≤ nrm ≤ C · rowNorm`, `c > 0`, where `rowNorm` is the `ℓ^∞`
  operator norm), with `c k ≤ g(k) ≤ 40 C k³`.
* `MF11.MF11_negative_answer_rowNorm`: the same for `rowNorm`, with `k ≤ g(k) ≤ 40 k³`.
* `MF11.dips_spectral` (the dips of Theorem 1.3, with a weaker but sufficient factor): for
  `p = pp j` (`j ≥ 1`) and `N = 16^p`, the spectral-norm sequence of `F20` satisfies
  `g(N/2) ≥ (p/400) g(N)` and `g(ℓN) ≥ ((ℓ - 1) p/400) g(N)` for every `ℓ ≥ 2`;
  `MF11.dips` is the same with the factors `p` and `(ℓ - 1) p` for `rowNorm`.

The only axioms used are `propext`, `Classical.choice` and `Quot.sound` (see the `#print axioms`
commands at the end of the file).

## How the file follows the paper

* §1–3 (`T5`, `NFv`, `NFv_comp`): the seven-dimensional algebra `𝒜` of Section 2 and the normal
  form of Lemma 2.3, written in the basis `e₀, …, e₆` (called `e₁, …, e₇` in the paper).
* §4–5 (`Sv`, `Tv`, `Jv`, `Lv`, `F0v`, `F1v`, `reduction`): the space `W = V ⊕ V ⊕ V_Y ⊕ V_Z`
  of dimension `20`, the maps `S, T, J, L` of Section 3.1, `F₀ = T S`, `F₁ = T J L S`, and the
  reduction of arbitrary products (Proposition 3.2).
* §6–7 (`Amat`, `rowNorm`, `growth`, `word_upper`, `crit_le_rowNorm`): the matrices, the norm,
  the sequence `g`, and the two-sided comparison of Corollary 3.4.
* §8–9 (`Dom`, `damped`, `undamped`, `Kt_pow`, `growth_bounds`): bounds for the coordinates of
  products of gap factors, and `n ≤ g(n) ≤ 40 n³` (Proposition 4.4, polynomial part, and
  Corollary 3.4(ii)).
* §10 (`pp`, `θs`, `q_nonres`, `q_res`): the Liouville angle `θ⋆ = 1/4 + 1/4⁴ + 1/4²⁵⁶ + ⋯` and
  the resonance / non-resonance estimates (Lemmas 4.2, 5.1 and 5.5 for `θ⋆`).
* §11–13 (`upper_at`, `lower_bound`, `dips`): the dip at the length `16^p`
  (Lemmas 4.5, 5.2, Proposition 5.3 and the proof of Theorem 1.3).
* §14–15: the two properties of the problem (Varney–Morris, Definition 4.1), the answer for
  `rowNorm` and for every comparable norm, and the `20 × 20` matrices `F20`.
* §16: the spectral norm (Mathlib's `Matrix.Norms.L2Operator`), the comparison
  `rowNorm A / 20 ≤ ‖A‖₂ ≤ 20 rowNorm A`, Theorem 1.3 for the spectral norm, and the problem
  exactly as posed.

## Differences from the paper

* Indexing: `pp 0 = 4` is the paper's `p₁`, so `j ≥ 1` here corresponds to `j ≥ 2` there.
* The upper bound at the length `16^p` is proved directly for `θ⋆`, with a uniform damping
  estimate for the non-resonant gap lengths (`damped`) instead of the general
  effective-multiplicity Lemma 4.3; the constants are therefore weaker than in the paper
  (the dip factor is `p`, or `p/400` for the spectral norm, instead of `2^p/(4·10⁵ p⁴)`), which
  is enough because `p → ∞`. Likewise the bounds `n ≤ g(n) ≤ 6n³` of the paper (Euclidean
  norm) appear as `n/20 ≤ g(n) ≤ 800 n³`.
* The proof works with the `ℓ^∞` operator norm `rowNorm`; §15–16 transfer the result to every
  norm, in particular to the spectral norm of the problem statement.
* Not formalized: Theorems 1.4–1.7 and Corollary 1.8 of the paper (invertible pairs, the
  almost-linear pair, and the positive results for two blocks and in dimension three).
-/

open Real

noncomputable section

namespace MF11

/-! ## 1. The truncated algebra -/

/-- `⟨P, y₁, y₂, z₁, z₂⟩` stands for `P·I + y₁·Y + y₂·Y² + z₁·Z + z₂·Z²`, where `Y, Z` commute,
`YZ = 0` and `Y³ = Z³ = 0`. -/
@[ext] structure T5 where
  P : ℝ
  y1 : ℝ
  y2 : ℝ
  z1 : ℝ
  z2 : ℝ

namespace T5

instance : One T5 := ⟨⟨1, 0, 0, 0, 0⟩⟩

instance : Mul T5 :=
  ⟨fun a b => ⟨a.P * b.P, a.P * b.y1 + a.y1 * b.P, a.P * b.y2 + a.y1 * b.y1 + a.y2 * b.P,
    a.P * b.z1 + a.z1 * b.P, a.P * b.z2 + a.z1 * b.z1 + a.z2 * b.P⟩⟩

@[simp] lemma one_P : (1 : T5).P = 1 := rfl
@[simp] lemma one_y1 : (1 : T5).y1 = 0 := rfl
@[simp] lemma one_y2 : (1 : T5).y2 = 0 := rfl
@[simp] lemma one_z1 : (1 : T5).z1 = 0 := rfl
@[simp] lemma one_z2 : (1 : T5).z2 = 0 := rfl
@[simp] lemma mul_P (a b : T5) : (a * b).P = a.P * b.P := rfl
@[simp] lemma mul_y1 (a b : T5) : (a * b).y1 = a.P * b.y1 + a.y1 * b.P := rfl
@[simp] lemma mul_y2 (a b : T5) : (a * b).y2 = a.P * b.y2 + a.y1 * b.y1 + a.y2 * b.P := rfl
@[simp] lemma mul_z1 (a b : T5) : (a * b).z1 = a.P * b.z1 + a.z1 * b.P := rfl
@[simp] lemma mul_z2 (a b : T5) : (a * b).z2 = a.P * b.z2 + a.z1 * b.z1 + a.z2 * b.P := rfl

instance : CommMonoid T5 where
  mul := (· * ·)
  one := 1
  mul_assoc a b c := by ext <;> simp only [mul_P, mul_y1, mul_y2, mul_z1, mul_z2] <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  mul_comm a b := by ext <;> simp only [mul_P, mul_y1, mul_y2, mul_z1, mul_z2] <;> ring

end T5

/-! ## 2. Gap factors -/

/-- `q θ m = cos (m π θ)`. -/
def q (θ : ℝ) (m : ℕ) : ℝ := cos (m * (π * θ))

/-- The gap factor `K_m = q_m I + 2^{-m} Y + 8^{-m} Z`. -/
def Kt (θ : ℝ) (m : ℕ) : T5 := ⟨q θ m, (1 / 2 : ℝ) ^ m, 0, (1 / 8 : ℝ) ^ m, 0⟩

/-- The critical coordinate `n z₂ - y₂`. -/
def crit (n : ℝ) (x : T5) : ℝ := n * x.z2 - x.y2

lemma crit_mul (n : ℝ) (x y : T5) :
    crit n (x * y) = x.P * crit n y + y.P * crit n x + (n * x.z1 * y.z1 - x.y1 * y.y1) := by
  simp only [crit, T5.mul_y2, T5.mul_z2]; ring

/-! ## 3. The action on `V = ℝ⁷` -/

abbrev V := Fin 7 → ℝ

/-- The action of `U^n (P + y₁Y + y₂Y² + z₁Z + z₂Z²)` on `ℝ⁷`, where (with basis `e₀,…,e₆`)
`X = E₃₀ + E₄₁ + E₅₂`, `Y = E₆₀ - E₅₆`, `Z = E₁₀ + E₂₁ + E₄₃ + E₅₄`, `U = I + X`. -/
def NFv (n : ℕ) (x : T5) (v : V) : V :=
  ![x.P * v 0,
    x.P * v 1 + x.z1 * v 0,
    x.P * v 2 + x.z1 * v 1 + x.z2 * v 0,
    x.P * v 3 + n * x.P * v 0,
    x.P * v 4 + n * x.P * v 1 + x.z1 * v 3 + n * x.z1 * v 0,
    x.P * v 5 + n * x.P * v 2 - x.y1 * v 6 + x.z1 * v 4 + n * x.z1 * v 1 + x.z2 * v 3
      + (n * x.z2 - x.y2) * v 0,
    x.P * v 6 + x.y1 * v 0]

lemma NFv_comp (n n' : ℕ) (x y : T5) (v : V) :
    NFv n x (NFv n' y v) = NFv (n + n') (x * y) v := by
  funext i
  fin_cases i <;> simp [NFv] <;> ring

lemma NFv_zero_one (v : V) : NFv 0 1 v = v := by
  funext i; fin_cases i <;> simp [NFv]

end MF11

namespace MF11

/-! ## 4. The space `W = V ⊕ V ⊕ V_Y ⊕ V_Z` (dimension 20) and the maps `S, T, J, L` -/

/-- Index type of `W`: two copies of `ℝ⁷`, then `V_Y ≅ ℝ²` (basis `e₅, e₆`) and
`V_Z ≅ ℝ⁴` (basis `e₁, e₂, e₄, e₅`). -/
abbrev ι := Fin 7 ⊕ (Fin 7 ⊕ (Fin 2 ⊕ Fin 4))

abbrev W := ι → ℝ

/-- Assemble a vector of `W` from its four blocks. -/
def mk (a b : V) (c : Fin 2 → ℝ) (d : Fin 4 → ℝ) : W := Sum.elim a (Sum.elim b (Sum.elim c d))

@[simp] lemma mk_1 (a b : V) (c : Fin 2 → ℝ) (d : Fin 4 → ℝ) (i : Fin 7) :
    mk a b c d (Sum.inl i) = a i := rfl
@[simp] lemma mk_2 (a b : V) (c : Fin 2 → ℝ) (d : Fin 4 → ℝ) (i : Fin 7) :
    mk a b c d (Sum.inr (Sum.inl i)) = b i := rfl
@[simp] lemma mk_3 (a b : V) (c : Fin 2 → ℝ) (d : Fin 4 → ℝ) (i : Fin 2) :
    mk a b c d (Sum.inr (Sum.inr (Sum.inl i))) = c i := rfl
@[simp] lemma mk_4 (a b : V) (c : Fin 2 → ℝ) (d : Fin 4 → ℝ) (i : Fin 4) :
    mk a b c d (Sum.inr (Sum.inr (Sum.inr i))) = d i := rfl

/-- `S^k`: rotation through the angle `kπθ` on the first two blocks, `2^{-k}` on `V_Y` and
`8^{-k}` on `V_Z`. -/
def Sv (θ : ℝ) (k : ℕ) (w : W) : W :=
  mk (fun i => cos (k * (π * θ)) * w (.inl i) - sin (k * (π * θ)) * w (.inr (.inl i)))
     (fun i => sin (k * (π * θ)) * w (.inl i) + cos (k * (π * θ)) * w (.inr (.inl i)))
     (fun i => (1 / 2 : ℝ) ^ k * w (.inr (.inr (.inl i))))
     (fun i => (1 / 8 : ℝ) ^ k * w (.inr (.inr (.inr i))))

/-- `U^n` restricted to `V_Z` in the basis `e₁, e₂, e₄, e₅`. -/
def UZ (n : ℕ) (d : Fin 4 → ℝ) : Fin 4 → ℝ := ![d 0, d 1, d 2 + n * d 0, d 3 + n * d 1]

/-- `T^n`: `U^n` on every block (`U` is the identity on `V_Y`). -/
def Tv (n : ℕ) (w : W) : W :=
  mk (NFv n 1 (fun i => w (.inl i))) (NFv n 1 (fun i => w (.inr (.inl i))))
     (fun i => w (.inr (.inr (.inl i)))) (UZ n (fun i => w (.inr (.inr (.inr i)))))

/-- `J v = (v, 0, Y v, Z v)`. -/
def Jv (v : V) : W := mk v 0 ![-v 6, v 0] ![v 0, v 1, v 3, v 4]

/-- inclusion `V_Y → V`. -/
def embY (c : Fin 2 → ℝ) : V := ![0, 0, 0, 0, 0, c 0, c 1]

/-- inclusion `V_Z → V`. -/
def embZ (d : Fin 4 → ℝ) : V := ![0, d 0, d 1, 0, d 2, d 3, 0]

/-- `L (w₁, w₂, w₃, w₄) = w₁ + w₃ + w₄`. -/
def Lv (w : W) : V := fun i =>
  w (.inl i) + embY (fun j => w (.inr (.inr (.inl j)))) i
    + embZ (fun j => w (.inr (.inr (.inr j)))) i

lemma Sv_Sv (θ : ℝ) (a b : ℕ) (w : W) : Sv θ a (Sv θ b w) = Sv θ (a + b) w := by
  funext i
  rcases i with i | i | i | i <;>
    simp only [Sv, mk_1, mk_2, mk_3, mk_4, Nat.cast_add, add_mul, cos_add, sin_add, pow_add] <;>
    ring

lemma Sv_zero (θ : ℝ) (w : W) : Sv θ 0 w = w := by
  funext i
  rcases i with i | i | i | i <;> simp [Sv]

lemma Tv_Sv (θ : ℝ) (n k : ℕ) (w : W) : Tv n (Sv θ k w) = Sv θ k (Tv n w) := by
  funext i
  rcases i with i | i | i | i
  · fin_cases i <;> simp [Tv, Sv, NFv] <;> ring
  · fin_cases i <;> simp [Tv, Sv, NFv] <;> ring
  · simp [Tv, Sv]
  · fin_cases i <;> simp [Tv, Sv, UZ] <;> ring

@[simp] lemma Tv_b1 (n : ℕ) (w : W) (i : Fin 7) :
    Tv n w (.inl i) = NFv n 1 (fun j => w (.inl j)) i := rfl
@[simp] lemma Tv_b2 (n : ℕ) (w : W) (i : Fin 7) :
    Tv n w (.inr (.inl i)) = NFv n 1 (fun j => w (.inr (.inl j))) i := rfl
@[simp] lemma Tv_b3 (n : ℕ) (w : W) (i : Fin 2) :
    Tv n w (.inr (.inr (.inl i))) = w (.inr (.inr (.inl i))) := rfl
@[simp] lemma Tv_b4 (n : ℕ) (w : W) (i : Fin 4) :
    Tv n w (.inr (.inr (.inr i))) = UZ n (fun j => w (.inr (.inr (.inr j)))) i := rfl

lemma Tv_Tv (n n' : ℕ) (w : W) : Tv n (Tv n' w) = Tv (n + n') w := by
  funext i
  rcases i with i | i | i | i
  · simp only [Tv_b1]; rw [NFv_comp, one_mul]
  · simp only [Tv_b2]; rw [NFv_comp, one_mul]
  · simp only [Tv_b3]
  · fin_cases i <;> simp [UZ] <;> ring

lemma Tv_zero (w : W) : Tv 0 w = w := by
  funext i
  rcases i with i | i | i | i
  · fin_cases i <;> simp [Tv, NFv]
  · fin_cases i <;> simp [Tv, NFv]
  · simp [Tv]
  · fin_cases i <;> simp [Tv, UZ]

lemma Tv_Jv (n : ℕ) (v : V) : Tv n (Jv v) = Jv (NFv n 1 v) := by
  funext i
  rcases i with i | i | i | i
  · simp [Tv, Jv]
  · fin_cases i <;> simp [Tv, Jv, NFv]
  · fin_cases i <;> simp [Tv, Jv, NFv]
  · fin_cases i <;> simp [Tv, Jv, NFv, UZ]

lemma Lv_Tv (n : ℕ) (w : W) : Lv (Tv n w) = NFv n 1 (Lv w) := by
  funext i
  fin_cases i <;> simp [Lv, Tv, NFv, UZ, embY, embZ] <;> ring

lemma Lv_Sv_Jv (θ : ℝ) (m : ℕ) (v : V) : Lv (Sv θ m (Jv v)) = NFv 0 (Kt θ m) v := by
  funext i
  fin_cases i <;> simp [Lv, Sv, Jv, NFv, Kt, q, embY, embZ]
  ring

end MF11

namespace MF11

/-! ## 5. Words and their reduction -/

/-- `F₀ = T S`. -/
def F0v (θ : ℝ) (w : W) : W := Tv 1 (Sv θ 1 w)

/-- `F₁ = T J L S`. -/
def F1v (θ : ℝ) (w : W) : W := Tv 1 (Jv (Lv (Sv θ 1 w)))

/-- The generator indexed by a letter. -/
def Fv (θ : ℝ) : Bool → W → W
  | false => F0v θ
  | true => F1v θ

/-- The product `F_{b₁} ∘ F_{b₂} ∘ ⋯` of a word `[b₁, b₂, …]` (the last letter acts first). -/
def wordv (θ : ℝ) : List Bool → W → W
  | [] => id
  | b :: l => Fv θ b ∘ wordv θ l

/-- Combinatorial data of a word: either no letter `1` (`pure k`, `k` letters), or
`mixed a b G`: `b` = position of the first letter `1` (counted from the right), `a` = number of
letters after the last letter `1`, and `G` = the gaps between consecutive letters `1`. -/
inductive St where
  | pure (k : ℕ)
  | mixed (a b : ℕ) (G : List ℕ)

def st : List Bool → St
  | [] => .pure 0
  | false :: l =>
      match st l with
      | .pure k => .pure (k + 1)
      | .mixed a b G => .mixed (a + 1) b G
  | true :: l =>
      match st l with
      | .pure k => .mixed 0 (k + 1) []
      | .mixed a b G => .mixed 0 b ((a + 1) :: G)

/-- **Reduction of words** (Proposition 3.2 of the paper). -/
theorem reduction (θ : ℝ) (l : List Bool) :
    (∀ k, st l = .pure k → k = l.length ∧ ∀ w, wordv θ l w = Tv k (Sv θ k w)) ∧
    (∀ a b G, st l = .mixed a b G → 1 ≤ b ∧ (∀ m ∈ G, 1 ≤ m) ∧ a + b + G.sum = l.length ∧
       ∀ w, wordv θ l w = Sv θ a (Jv (NFv l.length (G.map (Kt θ)).prod (Lv (Sv θ b w))))) := by
  induction l with
  | nil =>
    refine ⟨fun k hk => ?_, fun a b G h => ?_⟩
    · simp only [st, St.pure.injEq] at hk
      subst hk
      exact ⟨rfl, fun w => by simp [wordv, Tv_zero, Sv_zero]⟩
    · simp [st] at h
  | cons x l ih =>
    obtain ⟨ihp, ihm⟩ := ih
    cases x with
    | false =>
      cases hs : st l with
      | pure k =>
        obtain ⟨hk, hw⟩ := ihp k hs
        refine ⟨fun k' hk' => ?_, fun a b G h => ?_⟩
        · simp only [st, hs, St.pure.injEq] at hk'
          subst hk'
          refine ⟨by simp [hk], fun w => ?_⟩
          simp only [wordv, Function.comp_apply, Fv, F0v, hw]
          rw [← Tv_Sv, Sv_Sv, Tv_Tv, Nat.add_comm 1 k]
        · simp [st, hs] at h
      | mixed a b G =>
        obtain ⟨hb, hG, hsum, hw⟩ := ihm a b G hs
        refine ⟨fun k' hk' => ?_, fun a' b' G' h => ?_⟩
        · simp [st, hs] at hk'
        · simp only [st, hs, St.mixed.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          refine ⟨hb, hG, by simp only [List.length_cons]; omega, fun w => ?_⟩
          simp only [wordv, Function.comp_apply, Fv, F0v, hw, List.length_cons]
          rw [Sv_Sv, Tv_Sv, Tv_Jv, NFv_comp, one_mul, Nat.add_comm 1 a, Nat.add_comm 1]
    | true =>
      cases hs : st l with
      | pure k =>
        obtain ⟨hk, hw⟩ := ihp k hs
        refine ⟨fun k' hk' => ?_, fun a b G h => ?_⟩
        · simp [st, hs] at hk'
        · simp only [st, hs, St.mixed.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          refine ⟨by omega, by simp, by simp [hk], fun w => ?_⟩
          simp only [wordv, Function.comp_apply, Fv, F1v, hw, List.length_cons, List.map_nil,
            List.prod_nil]
          rw [← Tv_Sv, Sv_Sv, Lv_Tv, Tv_Jv, NFv_comp, Sv_zero, one_mul, Nat.add_comm 1 k, hk]
      | mixed a b G =>
        obtain ⟨hb, hG, hsum, hw⟩ := ihm a b G hs
        refine ⟨fun k' hk' => ?_, fun a' b' G' h => ?_⟩
        · simp [st, hs] at hk'
        · simp only [st, hs, St.mixed.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          refine ⟨hb, ?_, by simp only [List.length_cons, List.sum_cons]; omega, fun w => ?_⟩
          · intro m hm
            simp only [List.mem_cons] at hm
            rcases hm with rfl | hm
            · omega
            · exact hG m hm
          simp only [wordv, Function.comp_apply, Fv, F1v, hw, List.length_cons, List.map_cons,
            List.prod_cons]
          rw [Sv_Sv, Lv_Sv_Jv, NFv_comp, Tv_Jv, NFv_comp, Sv_zero, one_mul, zero_add,
            Nat.add_comm 1 a, Nat.add_comm 1]

end MF11

namespace MF11

open Matrix

/-! ## 6. Linearity, the two matrices, the norm and the growth sequence -/

lemma Sv_add (θ : ℝ) (k : ℕ) (u w : W) : Sv θ k (u + w) = Sv θ k u + Sv θ k w := by
  funext i; rcases i with i | i | i | i <;> simp [Sv] <;> ring

lemma Sv_smul (θ : ℝ) (k : ℕ) (c : ℝ) (w : W) : Sv θ k (c • w) = c • Sv θ k w := by
  funext i; rcases i with i | i | i | i <;> simp [Sv] <;> ring

lemma Tv_add (n : ℕ) (u w : W) : Tv n (u + w) = Tv n u + Tv n w := by
  funext i
  rcases i with i | i | i | i
  · fin_cases i <;> simp [NFv] <;> ring
  · fin_cases i <;> simp [NFv] <;> ring
  · simp
  · fin_cases i <;> simp [UZ] <;> ring

lemma Tv_smul (n : ℕ) (c : ℝ) (w : W) : Tv n (c • w) = c • Tv n w := by
  funext i
  rcases i with i | i | i | i
  · fin_cases i <;> simp [NFv] <;> ring
  · fin_cases i <;> simp [NFv] <;> ring
  · simp
  · fin_cases i <;> simp [UZ] <;> ring

lemma Jv_add (u v : V) : Jv (u + v) = Jv u + Jv v := by
  funext i
  rcases i with i | i | i | i
  · simp [Jv]
  · simp [Jv]
  · fin_cases i <;> simp [Jv]
    ring
  · fin_cases i <;> simp [Jv]

lemma Jv_smul (c : ℝ) (v : V) : Jv (c • v) = c • Jv v := by
  funext i
  rcases i with i | i | i | i
  · simp [Jv]
  · simp [Jv]
  · fin_cases i <;> simp [Jv]
  · fin_cases i <;> simp [Jv]

lemma Lv_add (u w : W) : Lv (u + w) = Lv u + Lv w := by
  funext i; fin_cases i <;> simp [Lv, embY, embZ] <;> ring

lemma Lv_smul (c : ℝ) (w : W) : Lv (c • w) = c • Lv w := by
  funext i; fin_cases i <;> simp [Lv, embY, embZ] <;> ring

/-- `F₀` as a linear map. -/
def F0L (θ : ℝ) : W →ₗ[ℝ] W where
  toFun := F0v θ
  map_add' u w := by simp only [F0v, Sv_add, Tv_add]
  map_smul' c w := by simp only [F0v, Sv_smul, Tv_smul, RingHom.id_apply]

/-- `F₁` as a linear map. -/
def F1L (θ : ℝ) : W →ₗ[ℝ] W where
  toFun := F1v θ
  map_add' u w := by simp only [F1v, Sv_add, Lv_add, Jv_add, Tv_add]
  map_smul' c w := by simp only [F1v, Sv_smul, Lv_smul, Jv_smul, Tv_smul, RingHom.id_apply]

/-- The two real `20 × 20` matrices `F₀(θ)` (letter `false`) and `F₁(θ)` (letter `true`). -/
def Amat (θ : ℝ) (b : Bool) : Matrix ι ι ℝ :=
  LinearMap.toMatrix' (if b then F1L θ else F0L θ)

lemma Amat_mulVec (θ : ℝ) (b : Bool) (w : W) : Amat θ b *ᵥ w = Fv θ b w := by
  cases b
  · show LinearMap.toMatrix' (F0L θ) *ᵥ w = F0v θ w
    rw [LinearMap.toMatrix'_mulVec]; rfl
  · show LinearMap.toMatrix' (F1L θ) *ᵥ w = F1v θ w
    rw [LinearMap.toMatrix'_mulVec]; rfl

lemma prod_mulVec (θ : ℝ) (l : List Bool) (w : W) :
    (l.map (Amat θ)).prod *ᵥ w = wordv θ l w := by
  induction l generalizing w with
  | nil => simp [wordv]
  | cons b l ih =>
    rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih, Amat_mulVec]
    rfl

/-- The `ℓ^∞` operator norm of a square matrix: the largest absolute row sum. -/
def rowNorm {n : Type*} [Fintype n] [Nonempty n] (A : Matrix n n ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => ∑ j, |A i j|

lemma abs_mulVec_le (A : Matrix ι ι ℝ) (v : W) (hv : ∀ j, |v j| ≤ 1) (i : ι) :
    |(A *ᵥ v) i| ≤ rowNorm A := by
  have h1 : |(A *ᵥ v) i| ≤ ∑ j, |A i j| := by
    simp only [Matrix.mulVec, dotProduct]
    calc |∑ j, A i j * v j| ≤ ∑ j, |A i j * v j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |A i j| := Finset.sum_le_sum fun j _ => by
          rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hv j)
  exact h1.trans (Finset.le_sup' (fun i => ∑ j, |A i j|) (Finset.mem_univ i))

lemma rowNorm_le (A : Matrix ι ι ℝ) (C : ℝ)
    (h : ∀ v : W, (∀ j, |v j| ≤ 1) → ∀ i, |(A *ᵥ v) i| ≤ C) : rowNorm A ≤ C := by
  refine Finset.sup'_le _ _ fun i _ => ?_
  let v : W := fun j => if 0 ≤ A i j then 1 else -1
  have hv : ∀ j, |v j| ≤ 1 := fun j => by simp only [v]; split_ifs <;> simp
  have hsum : (A *ᵥ v) i = ∑ j, |A i j| := by
    simp only [Matrix.mulVec, dotProduct, v]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h0
    · rw [mul_one, abs_of_nonneg h0]
    · rw [mul_neg_one, abs_of_neg (not_le.mp h0)]
  calc ∑ j, |A i j| = (A *ᵥ v) i := hsum.symm
    _ ≤ |(A *ᵥ v) i| := le_abs_self _
    _ ≤ C := h v hv i

/-- The marginal instability rate sequence for a norm `nrm`:
`g(n) = max {nrm (A_{b₁} ⋯ A_{bₙ}) : b ∈ {0,1}ⁿ}`. -/
def growth {m : Type*} [Fintype m] [DecidableEq m] (nrm : Matrix m m ℝ → ℝ)
    (A : Bool → Matrix m m ℝ) (n : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun w : Fin n → Bool => nrm ((List.ofFn w).map A).prod

lemma le_growth {m : Type*} [Fintype m] [DecidableEq m] (nrm : Matrix m m ℝ → ℝ)
    (A : Bool → Matrix m m ℝ) (l : List Bool) :
    nrm (l.map A).prod ≤ growth nrm A l.length := by
  have h := Finset.le_sup' (fun w : Fin l.length → Bool => nrm ((List.ofFn w).map A).prod)
    (Finset.mem_univ (fun i => l.get i))
  simp only [List.ofFn_get] at h
  exact h

lemma growth_le {m : Type*} [Fintype m] [DecidableEq m] (nrm : Matrix m m ℝ → ℝ)
    (A : Bool → Matrix m m ℝ) (n : ℕ) (C : ℝ)
    (h : ∀ l : List Bool, l.length = n → nrm (l.map A).prod ≤ C) : growth nrm A n ≤ C :=
  Finset.sup'_le _ _ fun _ _ => h _ (List.length_ofFn)

end MF11

namespace MF11

/-! ## 7. Norm bounds for reduced words -/

lemma abs_mul_le_of (a x C : ℝ) (ha : |a| ≤ 1) (hx : |x| ≤ C) : |a * x| ≤ C := by
  rw [abs_mul]
  calc |a| * |x| ≤ 1 * C := mul_le_mul ha hx (abs_nonneg _) zero_le_one
    _ = C := one_mul C

lemma abs_mul_le_mul (a x C : ℝ) (hx : |x| ≤ C) : |a * x| ≤ |a| * C := by
  rw [abs_mul]; exact mul_le_mul_of_nonneg_left hx (abs_nonneg a)

lemma Sv_bound (θ : ℝ) (k : ℕ) (w : W) (C : ℝ) (hw : ∀ j, |w j| ≤ C) (j : ι) :
    |Sv θ k w j| ≤ 2 * C := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hw (.inl 0))
  have h2 : |(1 / 2 : ℝ) ^ k| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have h8 : |(1 / 8 : ℝ) ^ k| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]; exact pow_le_one₀ (by norm_num) (by norm_num)
  rcases j with i | i | i | i
  · simp only [Sv, mk_1]
    have := abs_mul_le_of _ _ _ (abs_cos_le_one (k * (π * θ))) (hw (.inl i))
    have := abs_mul_le_of _ _ _ (abs_sin_le_one (k * (π * θ))) (hw (.inr (.inl i)))
    calc _ ≤ _ := abs_sub _ _
      _ ≤ C + C := add_le_add (by assumption) (by assumption)
      _ = 2 * C := by ring
  · simp only [Sv, mk_2]
    have := abs_mul_le_of _ _ _ (abs_sin_le_one (k * (π * θ))) (hw (.inl i))
    have := abs_mul_le_of _ _ _ (abs_cos_le_one (k * (π * θ))) (hw (.inr (.inl i)))
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ C + C := add_le_add (by assumption) (by assumption)
      _ = 2 * C := by ring
  · simp only [Sv, mk_3]
    linarith [abs_mul_le_of _ _ _ h2 (hw (.inr (.inr (.inl i))))]
  · simp only [Sv, mk_4]
    linarith [abs_mul_le_of _ _ _ h8 (hw (.inr (.inr (.inr i))))]

lemma Jv_bound (v : V) (C : ℝ) (hv : ∀ i, |v i| ≤ C) (j : ι) : |Jv v j| ≤ C := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hv 0)
  rcases j with i | i | i | i
  · simpa [Jv] using hv i
  · simpa [Jv] using hC
  · fin_cases i
    · simpa [Jv] using hv 6
    · simpa [Jv] using hv 0
  · fin_cases i
    · simpa [Jv] using hv 0
    · simpa [Jv] using hv 1
    · simpa [Jv] using hv 3
    · simpa [Jv] using hv 4

lemma Lv_bound (w : W) (C : ℝ) (hw : ∀ j, |w j| ≤ C) (i : Fin 7) : |Lv w i| ≤ 3 * C := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hw (.inl 0))
  have h1 := hw (.inl i)
  have h3 : |embY (fun j => w (.inr (.inr (.inl j)))) i| ≤ C := by
    fin_cases i <;> simp [embY, hC, hw]
  have h4 : |embZ (fun j => w (.inr (.inr (.inr j)))) i| ≤ C := by
    fin_cases i <;> simp [embZ, hC, hw]
  simp only [Lv]
  calc _ ≤ |w (.inl i) + embY (fun j => w (.inr (.inr (.inl j)))) i|
          + |embZ (fun j => w (.inr (.inr (.inr j)))) i| := abs_add_le _ _
    _ ≤ (|w (.inl i)| + |embY (fun j => w (.inr (.inr (.inl j)))) i|)
          + |embZ (fun j => w (.inr (.inr (.inr j)))) i| := by gcongr; exact abs_add_le _ _
    _ ≤ (C + C) + C := by gcongr
    _ = 3 * C := by ring

/-- The sum of the moduli of the seven coordinates of `U^n·x` applied to `e₀`. -/
def Mx (n : ℕ) (x : T5) : ℝ :=
  |x.P| + |(n : ℝ) * x.P| + |x.y1| + |x.z1| + |(n : ℝ) * x.z1| + |x.z2| + |(n : ℝ) * x.z2 - x.y2|

lemma Mx_nonneg (n : ℕ) (x : T5) : 0 ≤ Mx n x := by
  unfold Mx; positivity

lemma NFv_bound (n : ℕ) (x : T5) (v : V) (C : ℝ) (hv : ∀ i, |v i| ≤ C) (i : Fin 7) :
    |NFv n x v i| ≤ Mx n x * C := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hv 0)
  have b0 := abs_mul_le_mul x.P (v 0) C (hv 0)
  have b1 := abs_mul_le_mul x.P (v 1) C (hv 1)
  have b2 := abs_mul_le_mul x.P (v 2) C (hv 2)
  have b3 := abs_mul_le_mul x.P (v 3) C (hv 3)
  have b4 := abs_mul_le_mul x.P (v 4) C (hv 4)
  have b5 := abs_mul_le_mul x.P (v 5) C (hv 5)
  have b6 := abs_mul_le_mul x.P (v 6) C (hv 6)
  have c0 := abs_mul_le_mul x.z1 (v 0) C (hv 0)
  have c1 := abs_mul_le_mul x.z1 (v 1) C (hv 1)
  have c3 := abs_mul_le_mul x.z1 (v 3) C (hv 3)
  have c4 := abs_mul_le_mul x.z1 (v 4) C (hv 4)
  have d0 := abs_mul_le_mul x.z2 (v 0) C (hv 0)
  have d3 := abs_mul_le_mul x.z2 (v 3) C (hv 3)
  have e0 := abs_mul_le_mul x.y1 (v 0) C (hv 0)
  have e6 := abs_mul_le_mul x.y1 (v 6) C (hv 6)
  have f0 := abs_mul_le_mul ((n : ℝ) * x.P) (v 0) C (hv 0)
  have f1 := abs_mul_le_mul ((n : ℝ) * x.P) (v 1) C (hv 1)
  have f2 := abs_mul_le_mul ((n : ℝ) * x.P) (v 2) C (hv 2)
  have g0 := abs_mul_le_mul ((n : ℝ) * x.z1) (v 0) C (hv 0)
  have g1 := abs_mul_le_mul ((n : ℝ) * x.z1) (v 1) C (hv 1)
  have k0 := abs_mul_le_mul ((n : ℝ) * x.z2 - x.y2) (v 0) C (hv 0)
  have n1 : 0 ≤ |x.P| * C := by positivity
  have n2 : 0 ≤ |(n : ℝ) * x.P| * C := by positivity
  have n3 : 0 ≤ |x.y1| * C := by positivity
  have n4 : 0 ≤ |x.z1| * C := by positivity
  have n5 : 0 ≤ |(n : ℝ) * x.z1| * C := by positivity
  have n6 : 0 ≤ |x.z2| * C := by positivity
  have n7 : 0 ≤ |(n : ℝ) * x.z2 - x.y2| * C := by positivity
  simp only [Mx, add_mul]
  fin_cases i <;> simp only [NFv] <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val] <;>
    rw [abs_le] <;> constructor <;>
    linarith [abs_le.mp b0, abs_le.mp b1, abs_le.mp b2, abs_le.mp b3, abs_le.mp b4,
      abs_le.mp b5, abs_le.mp b6, abs_le.mp c0, abs_le.mp c1, abs_le.mp c3, abs_le.mp c4,
      abs_le.mp d0, abs_le.mp d3, abs_le.mp e0, abs_le.mp e6, abs_le.mp f0, abs_le.mp f1,
      abs_le.mp f2, abs_le.mp g0, abs_le.mp g1, abs_le.mp k0]

lemma Tv_bound (n : ℕ) (w : W) (C : ℝ) (hw : ∀ j, |w j| ≤ C) (j : ι) :
    |Tv n w j| ≤ (n + 1) * C := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hw (.inl 0))
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hM : Mx n 1 = n + 1 := by
    simp only [Mx, T5.one_P, T5.one_y1, T5.one_y2, T5.one_z1, T5.one_z2, mul_one, mul_zero,
      sub_zero, abs_one, abs_zero, add_zero, abs_of_nonneg hn]
    ring
  rcases j with i | i | i | i
  · rw [Tv_b1, ← hM]; exact NFv_bound n 1 _ C (fun i => hw _) i
  · rw [Tv_b2, ← hM]; exact NFv_bound n 1 _ C (fun i => hw _) i
  · rw [Tv_b3]; nlinarith [hw (.inr (.inr (.inl i)))]
  · rw [Tv_b4, add_one_mul]
    have b0 := abs_mul_le_mul (n : ℝ) (w (.inr (.inr (.inr 0)))) C (hw _)
    have b1 := abs_mul_le_mul (n : ℝ) (w (.inr (.inr (.inr 1)))) C (hw _)
    rw [abs_of_nonneg hn] at b0 b1
    have hnC : 0 ≤ (n : ℝ) * C := mul_nonneg hn hC
    have w0 := hw (.inr (.inr (.inr 0)))
    have w1 := hw (.inr (.inr (.inr 1)))
    have w2 := hw (.inr (.inr (.inr 2)))
    have w3 := hw (.inr (.inr (.inr 3)))
    fin_cases i <;> simp only [UZ] <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val] <;>
      rw [abs_le] <;> constructor <;>
      linarith [abs_le.mp b0, abs_le.mp b1, abs_le.mp w0, abs_le.mp w1, abs_le.mp w2,
        abs_le.mp w3]

end MF11

namespace MF11

/-! ## 8. Bounds for the coordinates of products of gap factors -/

/-- Majorant of a gap factor: `|q_m|` in place of `q_m`. -/
def Kab (θ : ℝ) (m : ℕ) : T5 := ⟨|q θ m|, (1 / 2 : ℝ) ^ m, 0, (1 / 8 : ℝ) ^ m, 0⟩

/-- `Dom x X`: every coordinate of `x` is bounded in modulus by that of `X`. -/
def Dom (x X : T5) : Prop :=
  |x.P| ≤ X.P ∧ |x.y1| ≤ X.y1 ∧ |x.y2| ≤ X.y2 ∧ |x.z1| ≤ X.z1 ∧ |x.z2| ≤ X.z2

lemma abs_add3_le (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| :=
  (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)

lemma Dom.mul {x X y Y : T5} (hx : Dom x X) (hy : Dom y Y) : Dom (x * y) (X * Y) := by
  obtain ⟨xP, xy1, xy2, xz1, xz2⟩ := hx
  obtain ⟨yP, yy1, yy2, yz1, yz2⟩ := hy
  have XP : 0 ≤ X.P := (abs_nonneg _).trans xP
  have Xy1 : 0 ≤ X.y1 := (abs_nonneg _).trans xy1
  have Xy2 : 0 ≤ X.y2 := (abs_nonneg _).trans xy2
  have Xz1 : 0 ≤ X.z1 := (abs_nonneg _).trans xz1
  have Xz2 : 0 ≤ X.z2 := (abs_nonneg _).trans xz2
  have m : ∀ {a b A B : ℝ}, |a| ≤ A → |b| ≤ B → 0 ≤ A → |a * b| ≤ A * B := fun ha hb hA => by
    rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) hA
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [T5.mul_P, T5.mul_y1, T5.mul_y2, T5.mul_z1, T5.mul_z2]
  · exact m xP yP XP
  · exact (abs_add_le _ _).trans (add_le_add (m xP yy1 XP) (m xy1 yP Xy1))
  · exact (abs_add3_le _ _ _).trans (add_le_add (add_le_add (m xP yy2 XP) (m xy1 yy1 Xy1))
      (m xy2 yP Xy2))
  · exact (abs_add_le _ _).trans (add_le_add (m xP yz1 XP) (m xz1 yP Xz1))
  · exact (abs_add3_le _ _ _).trans (add_le_add (add_le_add (m xP yz2 XP) (m xz1 yz1 Xz1))
      (m xz2 yP Xz2))

lemma dom_prod (θ : ℝ) (G : List ℕ) :
    Dom ((G.map (Kt θ)).prod) ((G.map (Kab θ)).prod) := by
  induction G with
  | nil => simp [Dom]
  | cons m G ih =>
    simp only [List.map_cons, List.prod_cons]
    refine Dom.mul ?_ ih
    refine ⟨le_rfl, ?_, by simp [Kt, Kab], ?_, by simp [Kt, Kab]⟩ <;>
      simp only [Kt, Kab] <;> rw [abs_of_nonneg (by positivity)]

lemma Kab_prod_nonneg (θ : ℝ) (G : List ℕ) :
    let X := (G.map (Kab θ)).prod
    0 ≤ X.P ∧ 0 ≤ X.y1 ∧ 0 ≤ X.y2 ∧ 0 ≤ X.z1 ∧ 0 ≤ X.z2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := dom_prod θ G
  exact ⟨(abs_nonneg _).trans h1, (abs_nonneg _).trans h2, (abs_nonneg _).trans h3,
    (abs_nonneg _).trans h4, (abs_nonneg _).trans h5⟩

/-- Products of gap factors whose cosines are uniformly bounded away from `±1`
(`|q_m| ≤ ρ` with `ρ D + 1 ≤ D`). -/
lemma damped (θ : ℝ) (G : List ℕ) (ρ D a b : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hD : ρ * D + 1 ≤ D)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hG : ∀ m ∈ G, |q θ m| ≤ ρ ∧ (1 / 2 : ℝ) ^ m ≤ a ∧ (1 / 8 : ℝ) ^ m ≤ b) :
    let X := (G.map (Kab θ)).prod
    X.P ≤ 1 ∧ X.y1 ≤ a * D ∧ X.y2 ≤ a ^ 2 * D ^ 2 ∧ X.z1 ≤ b * D ∧ X.z2 ≤ b ^ 2 * D ^ 2 := by
  have hD0 : 0 ≤ D := by nlinarith
  induction G with
  | nil =>
    simp only [List.map_nil, List.prod_nil, T5.one_P, T5.one_y1, T5.one_y2, T5.one_z1, T5.one_z2]
    exact ⟨le_rfl, by positivity, by positivity, by positivity, by positivity⟩
  | cons m G ih =>
    obtain ⟨hq, h2, h8⟩ := hG m (List.mem_cons_self ..)
    obtain ⟨iP, iy1, iy2, iz1, iz2⟩ := ih fun m' hm' => hG m' (List.mem_cons_of_mem _ hm')
    obtain ⟨nP, ny1, ny2, nz1, nz2⟩ := Kab_prod_nonneg θ G
    have hq0 : 0 ≤ |q θ m| := abs_nonneg _
    simp only [List.map_cons, List.prod_cons, T5.mul_P, T5.mul_y1, T5.mul_y2, T5.mul_z1,
      T5.mul_z2, Kab]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · nlinarith
    · nlinarith [mul_le_mul hq iy1 ny1 hρ, mul_le_mul h2 iP nP ha]
    · have h5 := mul_le_mul_of_nonneg_left hD (by positivity : (0 : ℝ) ≤ a ^ 2 * D)
      nlinarith [mul_le_mul hq iy2 ny2 hρ, mul_le_mul h2 iy1 ny1 ha]
    · nlinarith [mul_le_mul hq iz1 nz1 hρ, mul_le_mul h8 iP nP hb]
    · have h5 := mul_le_mul_of_nonneg_left hD (by positivity : (0 : ℝ) ≤ b ^ 2 * D)
      nlinarith [mul_le_mul hq iz2 nz2 hρ, mul_le_mul h8 iz1 nz1 hb]

/-- Products of gap factors without damping: bounds in terms of the number of factors. -/
lemma undamped (θ : ℝ) (G : List ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hG : ∀ m ∈ G, (1 / 2 : ℝ) ^ m ≤ a ∧ (1 / 8 : ℝ) ^ m ≤ b) :
    let X := (G.map (Kab θ)).prod
    X.P ≤ 1 ∧ X.y1 ≤ G.length * a ∧ X.y2 ≤ (G.length : ℝ) ^ 2 * a ^ 2 ∧ X.z1 ≤ G.length * b ∧
      X.z2 ≤ (G.length : ℝ) ^ 2 * b ^ 2 := by
  induction G with
  | nil => simp
  | cons m G ih =>
    obtain ⟨h2, h8⟩ := hG m (List.mem_cons_self ..)
    obtain ⟨iP, iy1, iy2, iz1, iz2⟩ := ih fun m' hm' => hG m' (List.mem_cons_of_mem _ hm')
    obtain ⟨nP, ny1, ny2, nz1, nz2⟩ := Kab_prod_nonneg θ G
    have hq : |q θ m| ≤ 1 := abs_cos_le_one _
    have hq0 : 0 ≤ |q θ m| := abs_nonneg _
    have hl : (0 : ℝ) ≤ G.length := Nat.cast_nonneg _
    simp only [List.map_cons, List.prod_cons, T5.mul_P, T5.mul_y1, T5.mul_y2, T5.mul_z1,
      T5.mul_z2, Kab, List.length_cons, Nat.cast_add, Nat.cast_one]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · nlinarith
    · nlinarith [mul_le_mul hq iy1 ny1 zero_le_one, mul_le_mul h2 iP nP ha]
    · nlinarith [mul_le_mul hq iy2 ny2 zero_le_one, mul_le_mul h2 iy1 ny1 ha]
    · nlinarith [mul_le_mul hq iz1 nz1 zero_le_one, mul_le_mul h8 iP nP hb]
    · nlinarith [mul_le_mul hq iz2 nz2 zero_le_one, mul_le_mul h8 iz1 nz1 hb]

@[simp] lemma Kt_P (θ : ℝ) (m : ℕ) : (Kt θ m).P = q θ m := rfl
@[simp] lemma Kt_y1 (θ : ℝ) (m : ℕ) : (Kt θ m).y1 = (1 / 2 : ℝ) ^ m := rfl
@[simp] lemma Kt_y2 (θ : ℝ) (m : ℕ) : (Kt θ m).y2 = 0 := rfl
@[simp] lemma Kt_z1 (θ : ℝ) (m : ℕ) : (Kt θ m).z1 = (1 / 8 : ℝ) ^ m := rfl
@[simp] lemma Kt_z2 (θ : ℝ) (m : ℕ) : (Kt θ m).z2 = 0 := rfl

/-- Exact identities for powers of one gap factor. -/
lemma Kt_pow (θ : ℝ) (p c : ℕ) :
    let x := Kt θ p ^ c
    x.P = q θ p ^ c ∧ q θ p * x.y1 = c * q θ p ^ c * (1 / 2 : ℝ) ^ p ∧
      q θ p ^ 2 * x.y2 = (c * (c - 1) / 2) * q θ p ^ c * ((1 / 2 : ℝ) ^ p) ^ 2 ∧
      x.z1 * (1 / 2 : ℝ) ^ p = x.y1 * (1 / 8 : ℝ) ^ p ∧
      x.z2 * ((1 / 2 : ℝ) ^ p) ^ 2 = x.y2 * ((1 / 8 : ℝ) ^ p) ^ 2 := by
  induction c with
  | zero => simp
  | succ c ih =>
    obtain ⟨hP, hy1, hy2, hz1, hz2⟩ := ih
    simp only [pow_succ, T5.mul_P, T5.mul_y1, T5.mul_y2, T5.mul_z1, T5.mul_z2, Kt_P, Kt_y1,
      Kt_y2, Kt_z1, Kt_z2, Nat.cast_add, Nat.cast_one]
    refine ⟨by rw [hP], ?_, ?_, ?_, ?_⟩
    · linear_combination (q θ p * (1 / 2 : ℝ) ^ p) * hP + q θ p * hy1
    · linear_combination (q θ p * (1 / 2 : ℝ) ^ p) * hy1 + q θ p * hy2
    · linear_combination q θ p * hz1
    · linear_combination ((1 / 2 : ℝ) ^ p * (1 / 8 : ℝ) ^ p) * hz1 + q θ p * hz2

end MF11

namespace MF11

open Matrix

/-! ## 9. Upper and lower bounds for the norm of one product -/

lemma abs_cos_add_abs_sin (x : ℝ) : 1 ≤ |cos x| + |sin x| := by
  have h := sin_sq_add_cos_sq x
  have hc := abs_cos_le_one x
  have hs := abs_sin_le_one x
  have hc2 : cos x ^ 2 = |cos x| ^ 2 := (sq_abs _).symm
  have hs2 : sin x ^ 2 = |sin x| ^ 2 := (sq_abs _).symm
  nlinarith [abs_nonneg (cos x), abs_nonneg (sin x)]

/-- The first basis vector of `V`. -/
def e0 : V := fun i => if i = 0 then 1 else 0

/-- A unit vector that `S^b` maps to `(e₀, 0, 0, 0)`. -/
def omega (θ : ℝ) (b : ℕ) : W :=
  mk (fun i => if i = 0 then cos (b * (π * θ)) else 0)
     (fun i => if i = 0 then -sin (b * (π * θ)) else 0) 0 0

lemma omega_bound (θ : ℝ) (b : ℕ) (j : ι) : |omega θ b j| ≤ 1 := by
  rcases j with i | i | i | i <;> simp only [omega, mk_1, mk_2, mk_3, mk_4]
  · split_ifs
    · exact abs_cos_le_one _
    · simp
  · split_ifs
    · rw [abs_neg]; exact abs_sin_le_one _
    · simp
  · simp
  · simp

lemma Sv_omega (θ : ℝ) (b : ℕ) : Sv θ b (omega θ b) = mk e0 0 0 0 := by
  funext i
  rcases i with i | i | i | i <;> simp only [Sv, omega, mk_1, mk_2, mk_3, mk_4, e0]
  · split_ifs
    · linear_combination sin_sq_add_cos_sq (b * (π * θ))
    · simp
  · split_ifs
    · simp only [Pi.zero_apply]; ring
    · simp
  · simp
  · simp

lemma Lv_mk_e0 : Lv (mk e0 0 0 0) = e0 := by
  funext i; fin_cases i <;> simp [Lv, embY, embZ, e0]

lemma NFv_e0_5 (n : ℕ) (x : T5) : NFv n x e0 5 = crit n x := by
  simp [NFv, e0, crit]

lemma NFv_e0_3 (n : ℕ) : NFv n 1 e0 3 = n := by
  simp [NFv, e0]

/-- The norm of a product is at least half the modulus of its critical coordinate. -/
lemma crit_le_rowNorm (θ : ℝ) (l : List Bool) (a b : ℕ) (G : List ℕ)
    (h : st l = .mixed a b G) :
    |crit l.length ((G.map (Kt θ)).prod)| ≤ 2 * rowNorm ((l.map (Amat θ)).prod) := by
  obtain ⟨-, -, -, hw⟩ := (reduction θ l).2 a b G h
  set A := (l.map (Amat θ)).prod
  set x := (G.map (Kt θ)).prod
  have hv := omega_bound θ b
  have key : A *ᵥ omega θ b = Sv θ a (Jv (NFv l.length x e0)) := by
    rw [prod_mulVec, hw, Sv_omega, Lv_mk_e0]
  have h1 := abs_mulVec_le A (omega θ b) hv (.inl 5)
  have h2 := abs_mulVec_le A (omega θ b) hv (.inr (.inl 5))
  rw [key] at h1 h2
  simp only [Sv, Jv, mk_1, mk_2, Pi.zero_apply, mul_zero, sub_zero, add_zero] at h1 h2
  rw [NFv_e0_5, abs_mul] at h1 h2
  have hcs := abs_cos_add_abs_sin (a * (π * θ))
  nlinarith [abs_nonneg (crit l.length x)]

lemma st_replicate_false (k : ℕ) : st (List.replicate k false) = .pure k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, st, ih]

/-- `‖F₀ⁿ‖ ≥ n`. -/
lemma pure_lower (θ : ℝ) (n : ℕ) :
    (n : ℝ) ≤ rowNorm (((List.replicate n false).map (Amat θ)).prod) := by
  obtain ⟨-, hw⟩ := (reduction θ (List.replicate n false)).1 n (st_replicate_false n)
  have h1 := abs_mulVec_le (((List.replicate n false).map (Amat θ)).prod) (omega θ n)
    (omega_bound θ n) (.inl 3)
  rw [prod_mulVec, hw, Sv_omega, Tv_b1] at h1
  have : (fun j => mk e0 0 0 0 (Sum.inl j)) = e0 := rfl
  rw [this, NFv_e0_3, abs_of_nonneg (Nat.cast_nonneg n)] at h1
  exact h1

/-- Upper bounds for the norm of a product, in terms of its reduced form. -/
lemma word_upper (θ : ℝ) (l : List Bool) :
    (∀ k, st l = .pure k → rowNorm ((l.map (Amat θ)).prod) ≤ 2 * (k + 1)) ∧
    (∀ a b G, st l = .mixed a b G →
      rowNorm ((l.map (Amat θ)).prod) ≤ 12 * Mx l.length ((G.map (Kt θ)).prod)) := by
  constructor
  · intro k hk
    obtain ⟨-, hw⟩ := (reduction θ l).1 k hk
    refine rowNorm_le _ _ fun v hv i => ?_
    rw [prod_mulVec, hw]
    have h1 := Sv_bound θ k v 1 hv
    have h2 := Tv_bound k (Sv θ k v) (2 * 1) h1 i
    linarith
  · intro a b G hG
    obtain ⟨-, -, -, hw⟩ := (reduction θ l).2 a b G hG
    refine rowNorm_le _ _ fun v hv i => ?_
    rw [prod_mulVec, hw]
    have h1 := Sv_bound θ b v 1 hv
    have h2 := Lv_bound (Sv θ b v) (2 * 1) h1
    have h3 := NFv_bound l.length ((G.map (Kt θ)).prod) _ (3 * (2 * 1)) h2
    have h4 := Jv_bound _ _ h3
    have h5 := Sv_bound θ a _ _ h4 i
    linarith

lemma Mx_le (n : ℕ) (x : T5) (P y1 z1 z2 Cr : ℝ) (hP : |x.P| ≤ P) (hy1 : |x.y1| ≤ y1)
    (hz1 : |x.z1| ≤ z1) (hz2 : |x.z2| ≤ z2) (hc : |crit n x| ≤ Cr) :
    Mx n x ≤ P + n * P + y1 + z1 + n * z1 + z2 + Cr := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have e1 : |(n : ℝ) * x.P| ≤ n * P := by
    rw [abs_mul, abs_of_nonneg hn]; exact mul_le_mul_of_nonneg_left hP hn
  have e2 : |(n : ℝ) * x.z1| ≤ n * z1 := by
    rw [abs_mul, abs_of_nonneg hn]; exact mul_le_mul_of_nonneg_left hz1 hn
  unfold Mx
  unfold crit at hc
  linarith

lemma sum_ge_length_mul (L : List ℕ) (k : ℕ) (h : ∀ m ∈ L, k ≤ m) : k * L.length ≤ L.sum := by
  induction L with
  | nil => simp
  | cons m L ih =>
    simp only [List.length_cons, List.sum_cons, Nat.mul_succ]
    have := h m (List.mem_cons_self ..)
    have := ih fun m' hm' => h m' (List.mem_cons_of_mem _ hm')
    omega

lemma sum_filter_le (L : List ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (L.filter P).sum ≤ L.sum := by
  induction L with
  | nil => simp
  | cons m L ih =>
    by_cases hm : P m
    · simp [hm]; omega
    · simp [hm]; omega

/-- **Polynomial bounds**: `n ≤ g(n) ≤ 40 n³`. -/
lemma growth_bounds (θ : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ≤ growth rowNorm (Amat θ) n ∧ growth rowNorm (Amat θ) n ≤ 40 * (n : ℝ) ^ 3 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h3 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hn'
  have h2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have h23 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by nlinarith
  constructor
  · have := le_growth rowNorm (Amat θ) (List.replicate n false)
    rw [List.length_replicate] at this
    exact (pure_lower θ n).trans this
  · refine growth_le _ _ _ _ fun l hl => ?_
    obtain ⟨hpure, hmixed⟩ := word_upper θ l
    cases hs : st l with
    | pure k =>
      obtain ⟨hk, -⟩ := (reduction θ l).1 k hs
      have := hpure k hs
      have hk' : (k : ℝ) = n := by rw [hk, hl]
      rw [hk'] at this
      linarith
    | mixed a b G =>
      obtain ⟨hb, hG, hsum, -⟩ := (reduction θ l).2 a b G hs
      have := hmixed a b G hs
      rw [hl] at this hsum
      set x := (G.map (Kt θ)).prod
      have hlen : G.length ≤ n := by
        have := sum_ge_length_mul G 1 hG
        omega
      have hlen' : (G.length : ℝ) ≤ n := by exact_mod_cast hlen
      have hl0 : (0 : ℝ) ≤ G.length := Nat.cast_nonneg _
      obtain ⟨dP, dy1, dy2, dz1, dz2⟩ := dom_prod θ G
      obtain ⟨uP, uy1, uy2, uz1, uz2⟩ := undamped θ G (1 / 2) (1 / 8) (by norm_num) (by norm_num)
        fun m hm => ⟨by
          calc (1 / 2 : ℝ) ^ m ≤ (1 / 2) ^ 1 :=
                pow_le_pow_of_le_one (by norm_num) (by norm_num) (hG m hm)
            _ = 1 / 2 := pow_one _, by
          calc (1 / 8 : ℝ) ^ m ≤ (1 / 8) ^ 1 :=
                pow_le_pow_of_le_one (by norm_num) (by norm_num) (hG m hm)
            _ = 1 / 8 := pow_one _⟩
      set X := (G.map (Kab θ)).prod
      have cP : |x.P| ≤ 1 := dP.trans uP
      have cy1 : |x.y1| ≤ n * (1 / 2) := dy1.trans (uy1.trans (by nlinarith))
      have cy2 : |x.y2| ≤ (n : ℝ) ^ 2 * (1 / 2) ^ 2 := dy2.trans (uy2.trans (by
        have : (G.length : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ hl0 hlen' 2
        nlinarith))
      have cz1 : |x.z1| ≤ n * (1 / 8) := dz1.trans (uz1.trans (by nlinarith))
      have cz2 : |x.z2| ≤ (n : ℝ) ^ 2 * (1 / 8) ^ 2 := dz2.trans (uz2.trans (by
        have : (G.length : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ hl0 hlen' 2
        nlinarith))
      have cc : |crit n x| ≤ n * ((n : ℝ) ^ 2 * (1 / 8) ^ 2) + (n : ℝ) ^ 2 * (1 / 2) ^ 2 := by
        unfold crit
        calc |(n : ℝ) * x.z2 - x.y2| ≤ |(n : ℝ) * x.z2| + |x.y2| := abs_sub _ _
          _ = n * |x.z2| + |x.y2| := by rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
          _ ≤ _ := by gcongr
      have hM := Mx_le n x _ _ _ _ _ cP cy1 cz1 cz2 cc
      linarith

end MF11

namespace MF11

/-! ## 10. The Liouville angle `θ⋆ = 1/4 + 1/4⁴ + 1/4^256 + ⋯` -/

/-- `pp 0 = 4`, `pp (j+1) = 4 ^ pp j` (the numbers `p₁, p₂, …` of the paper). -/
def pp : ℕ → ℕ
  | 0 => 4
  | j + 1 => 4 ^ pp j

/-- Exponents with `pp j = 2 ^ ee j`. -/
def ee : ℕ → ℕ
  | 0 => 2
  | j + 1 => 2 * pp j

lemma pp_eq (j : ℕ) : pp j = 2 ^ ee j := by
  cases j with
  | zero => rfl
  | succ j => rw [pp, ee, pow_mul]; norm_num

lemma pp_ge (j : ℕ) : 4 ≤ pp j := by
  induction j with
  | zero => exact le_rfl
  | succ j ih => exact Nat.le_self_pow (by omega) 4

lemma two_pp_le (j : ℕ) : 2 * pp j < pp (j + 1) := by
  show 2 * pp j < 4 ^ pp j
  calc 2 * pp j < 2 ^ (2 * pp j) := Nat.lt_two_pow_self
    _ = 4 ^ pp j := by rw [pow_mul]; norm_num

lemma pp_ge_mul (j i : ℕ) : 2 ^ i * pp j ≤ pp (j + i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have := two_pp_le (j + i)
    rw [pow_succ, ← add_assoc]
    nlinarith

lemma lt_pp (j : ℕ) : j < pp j := by
  induction j with
  | zero => simp [pp]
  | succ j ih => have := two_pp_le j; omega

lemma ee_ge (j : ℕ) (hj : 1 ≤ j) : 8 ≤ ee j := by
  obtain ⟨j, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have := pp_ge j
  simp only [ee]; omega

lemma ee_lt (j : ℕ) : ee j < ee (j + 1) := by
  have h1 : ee j < 2 ^ ee j := Nat.lt_two_pow_self
  rw [← pp_eq] at h1
  show ee j < 2 * pp j
  omega

lemma pp_succ_eq (j : ℕ) : pp (j + 1) = 2 ^ (ee (j + 1) - ee j) * pp j := by
  rw [pp_eq j, pp_eq (j + 1), ← pow_add, Nat.sub_add_cancel (ee_lt j).le]

/-- The numerators: `∑_{i ≤ j} 1/pp i = hh j / pp j`. -/
def hh : ℕ → ℕ
  | 0 => 1
  | j + 1 => hh j * 2 ^ (ee (j + 1) - ee j) + 1

lemma hh_odd (j : ℕ) : Odd (hh j) := by
  cases j with
  | zero => exact odd_one
  | succ j =>
    simp only [hh]
    refine Even.add_one (Even.mul_left ?_ _)
    exact (Nat.even_pow' (by have := ee_lt j; omega)).mpr even_two

lemma summable_inv_pp : Summable fun j => (1 : ℝ) / pp j := by
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    (summable_geometric_two.mul_left (1 / 4))
  have h : (2 : ℝ) ^ j * 4 ≤ pp j := by
    have := pp_ge_mul 0 j
    simp only [zero_add] at this
    have h0 : pp 0 = 4 := rfl
    rw [h0] at this
    exact_mod_cast this
  have h4 : (0 : ℝ) < 2 ^ j * 4 := by positivity
  calc (1 : ℝ) / pp j ≤ 1 / (2 ^ j * 4) := one_div_le_one_div_of_le h4 h
    _ = 1 / 4 * (1 / 2) ^ j := by rw [one_div_pow]; field_simp

/-- `θ⋆ = ∑ 1/pp j`. -/
def θs : ℝ := ∑' j, (1 : ℝ) / pp j

/-- `θ⋆ - ∑_{i ≤ j} 1/pp i`. -/
def tail (j : ℕ) : ℝ := ∑' i, (1 : ℝ) / pp (i + (j + 1))

lemma partial_sum (j : ℕ) :
    ∑ i ∈ Finset.range (j + 1), (1 : ℝ) / pp i = hh j / pp j := by
  induction j with
  | zero => simp [hh, pp]
  | succ j ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [hh]
    rw [pp_succ_eq j]
    have h1 : (pp j : ℝ) ≠ 0 := by
      have := pp_ge j; positivity
    push_cast
    field_simp

lemma θs_eq (j : ℕ) : θs = hh j / pp j + tail j := by
  rw [← partial_sum, θs, tail]
  exact (summable_inv_pp.sum_add_tsum_nat_add (j + 1)).symm

lemma summable_tail (j : ℕ) : Summable fun i => (1 : ℝ) / pp (i + (j + 1)) :=
  (summable_nat_add_iff (j + 1)).mpr summable_inv_pp

lemma tail_pos (j : ℕ) : 0 < tail j := by
  have h := (summable_tail j).le_tsum 0 (fun i _ => by positivity)
  have : (0 : ℝ) < 1 / pp (0 + (j + 1)) := by
    apply div_pos one_pos
    exact_mod_cast (by have := pp_ge (0 + (j + 1)); omega : 0 < pp (0 + (j + 1)))
  exact this.trans_le h

lemma tail_le (j : ℕ) : tail j ≤ 2 / pp (j + 1) := by
  have hp : (0 : ℝ) < pp (j + 1) := by
    exact_mod_cast (by have := pp_ge (j + 1); omega : 0 < pp (j + 1))
  have hle : ∀ i, (1 : ℝ) / pp (i + (j + 1)) ≤ 1 / pp (j + 1) * (1 / 2) ^ i := by
    intro i
    have h := pp_ge_mul (j + 1) i
    rw [show j + 1 + i = i + (j + 1) by ring] at h
    have h' : (2 : ℝ) ^ i * pp (j + 1) ≤ pp (i + (j + 1)) := by exact_mod_cast h
    have hpos : (0 : ℝ) < 2 ^ i * pp (j + 1) := by positivity
    calc (1 : ℝ) / pp (i + (j + 1)) ≤ 1 / (2 ^ i * pp (j + 1)) := one_div_le_one_div_of_le hpos h'
      _ = 1 / pp (j + 1) * (1 / 2) ^ i := by rw [one_div_pow]; field_simp
  calc tail j ≤ ∑' i : ℕ, 1 / (pp (j + 1) : ℝ) * (1 / 2) ^ i :=
        (summable_tail j).tsum_le_tsum hle (summable_geometric_two.mul_left _)
    _ = 2 / pp (j + 1) := by rw [tsum_mul_left, tsum_geometric_two]; ring

/-! ### Elementary bounds for the cosine -/

lemma cos_upper {x : ℝ} (hx : |x| ≤ 1) : cos x ≤ 1 - 43 / 96 * x ^ 2 := by
  have h := (abs_le.mp (Real.cos_bound hx)).2
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [abs_nonneg x, sq_abs x]
  have h4 : |x| ^ 4 ≤ x ^ 2 := by
    have : |x| ^ 4 = (x ^ 2) ^ 2 := by rw [← sq_abs x]; ring
    rw [this]; nlinarith [sq_nonneg x]
  linarith

lemma cos_lower {x : ℝ} (hx : |x| ≤ 1) : 1 - 53 / 96 * x ^ 2 ≤ cos x := by
  have h := (abs_le.mp (Real.cos_bound hx)).1
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [abs_nonneg x, sq_abs x]
  have h4 : |x| ^ 4 ≤ x ^ 2 := by
    have : |x| ^ 4 = (x ^ 2) ^ 2 := by rw [← sq_abs x]; ring
    rw [this]; nlinarith [sq_nonneg x]
  linarith

lemma abs_cos_mid_aux {δ y : ℝ} (hδ : 0 ≤ δ) (hy1 : δ ≤ y) (hy2 : y ≤ 1 / 2) :
    |cos (π * y)| ≤ cos (π * δ) := by
  have hpi := pi_pos
  have h0 : 0 ≤ cos (π * y) := cos_nonneg_of_mem_Icc ⟨by nlinarith, by nlinarith⟩
  rw [abs_of_nonneg h0]
  exact cos_le_cos_of_nonneg_of_le_pi (mul_nonneg hpi.le hδ) (by nlinarith) (by nlinarith)

lemma abs_cos_mid {δ y : ℝ} (hδ : 0 ≤ δ) (hy1 : δ ≤ y) (hy2 : y ≤ 1 - δ) :
    |cos (π * y)| ≤ cos (π * δ) := by
  rcases le_total y (1 / 2) with h | h
  · exact abs_cos_mid_aux hδ hy1 h
  · have : cos (π * y) = -cos (π * (1 - y)) := by
      rw [← cos_pi_sub]; ring_nf
    rw [this, abs_neg]
    exact abs_cos_mid_aux hδ (by linarith) (by linarith)

/-! ### Resonance and non-resonance -/

lemma four_pow_ge (x : ℕ) (hx : 4 ≤ x) : 8 * x ^ 2 ≤ 4 ^ x := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ x hx ih =>
    rw [pow_succ (4 : ℕ) x]
    nlinarith

lemma tail_bound (j : ℕ) :
    0 < tail j ∧ tail j ≤ 2 / (4 : ℝ) ^ pp j := by
  refine ⟨tail_pos j, ?_⟩
  have := tail_le j
  have e : ((pp (j + 1) : ℕ) : ℝ) = (4 : ℝ) ^ pp j := by
    show ((4 ^ pp j : ℕ) : ℝ) = (4 : ℝ) ^ pp j
    push_cast; ring
  rwa [e] at this

/-- Non-resonance: `|cos (π m θ⋆)| ≤ 1 - 1/(4p²)` for `1 ≤ m < 2p`, `m ≠ p`, `p = pp j`. -/
lemma q_nonres (j : ℕ) (m : ℕ) (hm1 : 1 ≤ m) (hm2 : m < 2 * pp j) (hmp : m ≠ pp j) :
    |q θs m| ≤ 1 - 1 / (4 * (pp j : ℝ) ^ 2) := by
  set p := pp j with hpdef
  set h := hh j
  set ε := tail j
  have hp4 : 4 ≤ p := pp_ge j
  have hpR : (4 : ℝ) ≤ p := by exact_mod_cast hp4
  have hp0 : (0 : ℝ) < p := by linarith
  have hpne : (p : ℝ) ≠ 0 := hp0.ne'
  obtain ⟨hε0, hε1⟩ := tail_bound j
  -- `m h = p K + r` with `0 < r < p`
  set H := m * h
  set K := H / p
  set r := H % p
  have hHr : H = p * K + r := (Nat.div_add_mod H p).symm
  have hr_lt : r < p := Nat.mod_lt _ (by omega)
  have hr_pos : r ≠ 0 := by
    intro hr0
    have hdvd : p ∣ m * h := Nat.dvd_of_mod_eq_zero hr0
    have hcop : Nat.Coprime p h := by
      rw [hpdef, pp_eq]
      exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (hh_odd j))
    obtain ⟨t, ht⟩ := hcop.dvd_of_dvd_mul_right hdvd
    have ht0 : t ≠ 0 := by rintro rfl; simp at ht; omega
    have ht2 : t < 2 := by
      by_contra hcon
      have hcon : 2 ≤ t := by omega
      have := Nat.mul_le_mul_left p hcon
      rw [← ht] at this
      omega
    have : t = 1 := by omega
    subst this
    simp at ht
    exact hmp ht
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr_pos
  have hr2 : (r : ℝ) ≤ p - 1 := by
    have : r + 1 ≤ p := hr_lt
    have : ((r + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast this
    push_cast at this; linarith
  -- `m θ⋆ = K + y`
  set y : ℝ := r / p + m * ε
  have hmθ : (m : ℝ) * θs = K + y := by
    rw [θs_eq j]
    have hH' : ((m * h : ℕ) : ℝ) = p * K + r := by
      have : m * h = p * K + r := hHr
      exact_mod_cast this
    push_cast at hH'
    calc (m : ℝ) * ((h : ℝ) / p + ε) = (m * h) / p + m * ε := by ring
      _ = (p * K + r) / p + m * ε := by rw [hH']
      _ = K + y := by rw [add_div, mul_div_cancel_left₀ _ hpne]; ring
  have hq : |q θs m| = |cos (π * y)| := by
    have e : (m : ℝ) * (π * θs) = π * y + K * π := by
      rw [← mul_assoc, mul_comm (m : ℝ) π, mul_assoc, hmθ]; ring
    rw [q, e, cos_add_nat_mul_pi, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  -- `m ε ≤ 1/(2p)`
  have hmε : (m : ℝ) * ε ≤ 1 / (2 * p) := by
    have hm : (m : ℝ) ≤ 2 * p := by exact_mod_cast hm2.le
    have h48 : (8 : ℝ) * p ^ 2 ≤ 4 ^ p := by exact_mod_cast four_pow_ge p hp4
    have h4p : (0 : ℝ) < 4 ^ p := by positivity
    calc (m : ℝ) * ε ≤ 2 * p * (2 / 4 ^ p) := by
          apply mul_le_mul hm hε1 hε0.le (by positivity)
      _ = 4 * p / 4 ^ p := by ring
      _ ≤ 1 / (2 * p) := by
          rw [div_le_div_iff₀ h4p (by positivity)]
          nlinarith
  have hmε0 : 0 ≤ (m : ℝ) * ε := by positivity
  have hy1 : 1 / (2 * p) ≤ y := by
    have : 1 / (2 * (p : ℝ)) ≤ r / p := by
      rw [div_le_div_iff₀ (by positivity) hp0]; nlinarith
    simp only [y]; linarith
  have hy2 : y ≤ 1 - 1 / (2 * p) := by
    have : (r : ℝ) / p ≤ 1 - 1 / p := by
      rw [div_le_iff₀ hp0, sub_mul, div_mul_cancel₀ _ hpne]; linarith
    have : 1 / (p : ℝ) = 2 * (1 / (2 * p)) := by field_simp
    simp only [y]; linarith
  have hδ : (0 : ℝ) ≤ 1 / (2 * p) := by positivity
  have hmid := abs_cos_mid hδ hy1 hy2
  have hx : |π * (1 / (2 * p))| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    rw [show π * (1 / (2 * (p : ℝ))) = π / (2 * p) by ring, div_le_one (by positivity)]
    nlinarith [pi_le_four]
  have hup := cos_upper hx
  have hsq : 1 / (p : ℝ) ^ 2 ≤ (π * (1 / (2 * p))) ^ 2 := by
    rw [show π * (1 / (2 * (p : ℝ))) = π / (2 * p) by ring, div_pow,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hpi2 : 4 ≤ π ^ 2 := by nlinarith [two_le_pi]
    nlinarith [mul_le_mul_of_nonneg_right hpi2 (sq_nonneg (p : ℝ))]
  rw [hq]
  have : 1 / (4 * (p : ℝ) ^ 2) ≤ 43 / 96 * (1 / (p : ℝ) ^ 2) := by
    rw [show 1 / (4 * (p : ℝ) ^ 2) = (1 / 4) * (1 / (p : ℝ) ^ 2) by field_simp]
    have : 0 ≤ 1 / (p : ℝ) ^ 2 := by positivity
    nlinarith
  nlinarith

/-- Resonance: `|cos (π p θ⋆)| ≥ 1 - 36 p²/16^p` for `p = pp j`. -/
lemma q_res (j : ℕ) : 1 - 36 * (pp j : ℝ) ^ 2 / 16 ^ pp j ≤ |q θs (pp j)| := by
  set p := pp j with hpdef
  set h := hh j
  set ε := tail j
  have hp4 : 4 ≤ p := pp_ge j
  have hpR : (4 : ℝ) ≤ p := by exact_mod_cast hp4
  have hp0 : (0 : ℝ) < p := by linarith
  have hpne : (p : ℝ) ≠ 0 := hp0.ne'
  obtain ⟨hε0, hε1⟩ := tail_bound j
  have hpθ : (p : ℝ) * θs = h + p * ε := by
    rw [θs_eq j]
    calc (p : ℝ) * ((h : ℝ) / p + ε) = p * ((h : ℝ) / p) + p * ε := by ring
      _ = h + p * ε := by congr 1; field_simp
  have hq : |q θs p| = |cos (π * (p * ε))| := by
    have e : (p : ℝ) * (π * θs) = π * (p * ε) + h * π := by
      rw [← mul_assoc, mul_comm (p : ℝ) π, mul_assoc, hpθ]; ring
    rw [q, e, cos_add_nat_mul_pi, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have h48 : (8 : ℝ) * p ^ 2 ≤ 4 ^ p := by exact_mod_cast four_pow_ge p hp4
  have h4p : (0 : ℝ) < 4 ^ p := by positivity
  have hpε : (p : ℝ) * ε ≤ 2 * p / 4 ^ p := by
    calc (p : ℝ) * ε ≤ p * (2 / 4 ^ p) := mul_le_mul_of_nonneg_left hε1 hp0.le
      _ = 2 * p / 4 ^ p := by ring
  have hpε0 : 0 ≤ (p : ℝ) * ε := by positivity
  have hx : |π * (p * ε)| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    have : (2 : ℝ) * p / 4 ^ p ≤ 1 / 4 := by
      rw [div_le_div_iff₀ h4p (by norm_num)]; nlinarith
    nlinarith [pi_le_four, pi_pos]
  have hlow := cos_lower hx
  have h16 : (16 : ℝ) ^ p = (4 ^ p) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hsq : (π * (p * ε)) ^ 2 ≤ 64 * p ^ 2 / 16 ^ p := by
    rw [h16]
    have h1 : (π * (p * ε)) ^ 2 ≤ (4 * (2 * p / 4 ^ p)) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      exact mul_le_mul pi_le_four hpε hpε0 (by norm_num)
    calc (π * (p * ε)) ^ 2 ≤ (4 * (2 * p / 4 ^ p)) ^ 2 := h1
      _ = 64 * p ^ 2 / (4 ^ p) ^ 2 := by field_simp; ring
  rw [hq]
  have hsq1 : (π * (p * ε)) ^ 2 ≤ 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (π * (p * ε))]
  have h0 : 0 ≤ cos (π * (p * ε)) := by linarith
  rw [abs_of_nonneg h0]
  have : (0 : ℝ) ≤ p ^ 2 / 16 ^ p := by positivity
  have e : 36 * (p : ℝ) ^ 2 / 16 ^ p = 36 * (p ^ 2 / 16 ^ p) := by ring
  have e2 : 64 * (p : ℝ) ^ 2 / 16 ^ p = 64 * (p ^ 2 / 16 ^ p) := by ring
  rw [e]; rw [e2] at hsq
  nlinarith

end MF11

namespace MF11

open Filter Topology

/-! ## 11. The upper bound at the lengths `N = 16^p` -/

lemma lin_le_two_pow (e : ℕ) (he : 8 ≤ e) : 33 + 7 * e ≤ 2 ^ e := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ e he ih =>
    rw [pow_succ]
    have : 7 ≤ 2 ^ e := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) he)
    omega

/-- `2^33 p^7 ≤ 2^p` for `p = pp j`, `j ≥ 1`. -/
lemma exp_beats_poly (j : ℕ) (hj : 1 ≤ j) : (2 : ℝ) ^ 33 * (pp j : ℝ) ^ 7 ≤ 2 ^ pp j := by
  have he := ee_ge j hj
  have h := lin_le_two_pow (ee j) he
  have hpe := pp_eq j
  have : (2 : ℝ) ^ 33 * ((2 : ℝ) ^ ee j) ^ 7 = 2 ^ (33 + 7 * ee j) := by
    rw [← pow_mul, ← pow_add, mul_comm (ee j) 7]
  rw [hpe]
  push_cast
  rw [this]
  exact pow_le_pow_right₀ (by norm_num) h

lemma pp_ge_256 (j : ℕ) (hj : 1 ≤ j) : 256 ≤ pp j := by
  rw [pp_eq]
  calc 256 = 2 ^ 8 := by norm_num
    _ ≤ 2 ^ ee j := Nat.pow_le_pow_right (by norm_num) (ee_ge j hj)

lemma split3 (θ : ℝ) (G : List ℕ) (p : ℕ) :
    (G.map (Kt θ)).prod = ((G.filter (· = p)).map (Kt θ)).prod *
      ((((G.filter (fun m => ¬ m = p)).filter (· < 2 * p)).map (Kt θ)).prod *
       (((G.filter (fun m => ¬ m = p)).filter (fun m => ¬ m < 2 * p)).map (Kt θ)).prod) := by
  rw [List.prod_map_filter_mul_prod_map_filter_not, List.prod_map_filter_mul_prod_map_filter_not]

/-- Bounds for a product in the truncated algebra, from bounds on the factors. -/
lemma T5_mul_le {X Y : T5} {p1 a1 a2 b1 b2 p1' a1' a2' b1' b2' : ℝ}
    (hX : 0 ≤ X.P ∧ 0 ≤ X.y1 ∧ 0 ≤ X.y2 ∧ 0 ≤ X.z1 ∧ 0 ≤ X.z2)
    (hY : 0 ≤ Y.P ∧ 0 ≤ Y.y1 ∧ 0 ≤ Y.y2 ∧ 0 ≤ Y.z1 ∧ 0 ≤ Y.z2)
    (bX : X.P ≤ p1 ∧ X.y1 ≤ a1 ∧ X.y2 ≤ a2 ∧ X.z1 ≤ b1 ∧ X.z2 ≤ b2)
    (bY : Y.P ≤ p1' ∧ Y.y1 ≤ a1' ∧ Y.y2 ≤ a2' ∧ Y.z1 ≤ b1' ∧ Y.z2 ≤ b2') :
    (X * Y).P ≤ p1 * p1' ∧ (X * Y).y1 ≤ p1 * a1' + a1 * p1' ∧
      (X * Y).y2 ≤ p1 * a2' + a1 * a1' + a2 * p1' ∧ (X * Y).z1 ≤ p1 * b1' + b1 * p1' ∧
      (X * Y).z2 ≤ p1 * b2' + b1 * b1' + b2 * p1' := by
  obtain ⟨x1, x2, x3, x4, x5⟩ := hX
  obtain ⟨y1, y2, y3, y4, y5⟩ := hY
  obtain ⟨c1, c2, c3, c4, c5⟩ := bX
  obtain ⟨d1, d2, d3, d4, d5⟩ := bY
  have m : ∀ {a b c d : ℝ}, a ≤ b → c ≤ d → 0 ≤ a → 0 ≤ c → a * c ≤ b * d :=
    fun h1 h2 ha hc => mul_le_mul h1 h2 hc (ha.trans h1)
  simp only [T5.mul_P, T5.mul_y1, T5.mul_y2, T5.mul_z1, T5.mul_z2]
  refine ⟨m c1 d1 x1 y1, add_le_add (m c1 d2 x1 y2) (m c2 d1 x2 y1),
    add_le_add (add_le_add (m c1 d3 x1 y3) (m c2 d2 x2 y2)) (m c3 d1 x3 y1),
    add_le_add (m c1 d4 x1 y4) (m c4 d1 x4 y1),
    add_le_add (add_le_add (m c1 d5 x1 y5) (m c4 d4 x4 y4)) (m c5 d1 x5 y1)⟩

lemma abs_mul_le' {a b A' B' : ℝ} (ha : |a| ≤ A') (hb : |b| ≤ B') : |a * b| ≤ A' * B' := by
  rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

/-- Facts about `A = 2^p`, `a = 2^{-p}`, `b = 8^{-p}`. -/
lemma pow_facts (p : ℕ) :
    ((1 / 2 : ℝ) ^ p) * (2 : ℝ) ^ p = 1 ∧ ((1 / 8 : ℝ) ^ p) * ((2 : ℝ) ^ p) ^ 3 = 1 ∧
      ((16 ^ p : ℕ) : ℝ) = ((2 : ℝ) ^ p) ^ 4 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← mul_pow]; norm_num
  · rw [← pow_mul, mul_comm p 3, pow_mul, ← mul_pow]; norm_num
  · push_cast; rw [← pow_mul, mul_comm, pow_mul]; norm_num

/-- The resonant gaps: `c` gaps of length `p`, with `c p ≤ 16^p`. -/
lemma resonant_part (θ : ℝ) (p c : ℕ) (hc : c * p ≤ 16 ^ p) (hp : 1 ≤ p) :
    |(Kt θ p ^ c).P| ≤ 1 ∧ |(Kt θ p ^ c).y1| ≤ ((2 : ℝ) ^ p) ^ 3 ∧
      |(Kt θ p ^ c).z1| ≤ (2 : ℝ) ^ p ∧ |(Kt θ p ^ c).z2| ≤ ((2 : ℝ) ^ p) ^ 2 ∧
      crit ((16 ^ p : ℕ) : ℝ) (Kt θ p ^ c) = 0 := by
  obtain ⟨haA, hbA, hN⟩ := pow_facts p
  set A : ℝ := (2 : ℝ) ^ p
  set a : ℝ := (1 / 2 : ℝ) ^ p with hadef
  set b : ℝ := (1 / 8 : ℝ) ^ p with hbdef
  have hA1 : (1 : ℝ) ≤ A := one_le_pow₀ (by norm_num)
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := by positivity
  have hcA : (c : ℝ) ≤ A ^ 4 := by
    have : ((c * p : ℕ) : ℝ) ≤ ((16 ^ p : ℕ) : ℝ) := by exact_mod_cast hc
    rw [hN] at this; push_cast at this
    have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
    nlinarith [Nat.cast_nonneg (α := ℝ) c]
  have hlist : Kt θ p ^ c = ((List.replicate c p).map (Kt θ)).prod := by
    rw [List.map_replicate, List.prod_replicate]
  obtain ⟨dP, dy1, -, dz1, dz2⟩ := dom_prod θ (List.replicate c p)
  obtain ⟨uP, uy1, -, uz1, uz2⟩ := undamped θ (List.replicate c p) a b ha0.le hb0.le
    fun m hm => by
      rw [(List.mem_replicate.mp hm).2]
      exact ⟨le_of_eq hadef.symm, le_of_eq hbdef.symm⟩
  rw [List.length_replicate] at uy1 uz1 uz2
  rw [← hlist] at dP dy1 dz1 dz2
  have e1 : (c : ℝ) * a ≤ A ^ 3 := by
    calc (c : ℝ) * a ≤ A ^ 4 * a := mul_le_mul_of_nonneg_right hcA ha0.le
      _ = A ^ 3 * (a * A) := by ring
      _ = A ^ 3 := by rw [haA, mul_one]
  have e2 : (c : ℝ) * b ≤ A := by
    calc (c : ℝ) * b ≤ A ^ 4 * b := mul_le_mul_of_nonneg_right hcA hb0.le
      _ = A * (b * A ^ 3) := by ring
      _ = A := by rw [hbA, mul_one]
  refine ⟨dP.trans uP, dy1.trans (uy1.trans e1), dz1.trans (uz1.trans e2), dz2.trans ?_, ?_⟩
  · calc _ ≤ (c : ℝ) ^ 2 * b ^ 2 := uz2
      _ = ((c : ℝ) * b) ^ 2 := by ring
      _ ≤ A ^ 2 := pow_le_pow_left₀ (by positivity) e2 2
  · obtain ⟨-, -, -, -, hz2⟩ := Kt_pow θ p c
    have hNb : A ^ 4 * b ^ 2 = a ^ 2 := by
      have : A ^ 4 * b ^ 2 * A ^ 2 = a ^ 2 * A ^ 2 := by
        have e1 : A ^ 4 * b ^ 2 * A ^ 2 = (b * A ^ 3) ^ 2 := by ring
        have e2 : a ^ 2 * A ^ 2 = (a * A) ^ 2 := by ring
        rw [e1, e2, hbA, haA]
      exact mul_right_cancel₀ (by positivity : A ^ 2 ≠ 0) this
    unfold crit
    rw [hN]
    have : (A ^ 4 * (Kt θ p ^ c).z2 - (Kt θ p ^ c).y2) * a ^ 2 = 0 := by
      linear_combination A ^ 4 * hz2 + (Kt θ p ^ c).y2 * hNb
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h (by positivity)

/-- The non-resonant short gaps. -/
lemma nonres_part (j : ℕ) (GS : List ℕ)
    (hGS : ∀ m ∈ GS, 1 ≤ m ∧ m < 2 * pp j ∧ m ≠ pp j) :
    ((GS.map (Kab θs)).prod).P ≤ 1 ∧ ((GS.map (Kab θs)).prod).y1 ≤ 2 * (pp j : ℝ) ^ 2 ∧
      ((GS.map (Kab θs)).prod).y2 ≤ 4 * (pp j : ℝ) ^ 4 ∧
      ((GS.map (Kab θs)).prod).z1 ≤ (pp j : ℝ) ^ 2 / 2 ∧
      ((GS.map (Kab θs)).prod).z2 ≤ (pp j : ℝ) ^ 4 / 4 := by
  set P : ℝ := (pp j : ℝ) with hPdef
  have hP4 : (4 : ℝ) ≤ P := by rw [hPdef]; exact_mod_cast pp_ge j
  obtain ⟨u1, u2, u3, u4, u5⟩ := damped θs GS (1 - 1 / (4 * P ^ 2)) (4 * P ^ 2) (1 / 2) (1 / 8)
    (by
      have : 1 / (4 * P ^ 2) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
      linarith)
    (by
      have : 0 ≤ 1 / (4 * P ^ 2) := by positivity
      linarith)
    (by
      have : (1 - 1 / (4 * P ^ 2)) * (4 * P ^ 2) = 4 * P ^ 2 - 1 := by
        field_simp
      linarith)
    (by norm_num) (by norm_num) fun m hm => by
      obtain ⟨hm1, hm2, hm3⟩ := hGS m hm
      refine ⟨q_nonres j m hm1 hm2 hm3, ?_, ?_⟩
      · calc (1 / 2 : ℝ) ^ m ≤ (1 / 2) ^ 1 :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) hm1
          _ = 1 / 2 := pow_one _
      · calc (1 / 8 : ℝ) ^ m ≤ (1 / 8) ^ 1 :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) hm1
          _ = 1 / 8 := pow_one _
  refine ⟨u1, u2.trans (le_of_eq (by ring)), u3.trans (le_of_eq (by ring)),
    u4.trans (le_of_eq (by ring)), u5.trans (le_of_eq (by ring))⟩

/-- The long gaps (`m ≥ 2p`). -/
lemma big_part (θ : ℝ) (p : ℕ) (GB : List ℕ) (hGB : ∀ m ∈ GB, 2 * p ≤ m)
    (hlen : GB.length * (2 * p) ≤ 16 ^ p) (hp : 1 ≤ p) :
    ((GB.map (Kab θ)).prod).P ≤ 1 ∧ ((GB.map (Kab θ)).prod).y1 ≤ ((2 : ℝ) ^ p) ^ 2 ∧
      ((GB.map (Kab θ)).prod).y2 ≤ ((2 : ℝ) ^ p) ^ 4 ∧ ((GB.map (Kab θ)).prod).z1 ≤ 1 ∧
      ((GB.map (Kab θ)).prod).z2 ≤ 1 := by
  obtain ⟨haA, hbA, hN⟩ := pow_facts p
  set A : ℝ := (2 : ℝ) ^ p
  set a : ℝ := (1 / 2 : ℝ) ^ p with hadef
  set b : ℝ := (1 / 8 : ℝ) ^ p with hbdef
  have hA1 : (1 : ℝ) ≤ A := one_le_pow₀ (by norm_num)
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := by positivity
  set h := GB.length
  have hBA : (h : ℝ) ≤ A ^ 4 := by
    have : ((h * (2 * p) : ℕ) : ℝ) ≤ ((16 ^ p : ℕ) : ℝ) := by exact_mod_cast hlen
    rw [hN] at this; push_cast at this
    have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
    nlinarith [Nat.cast_nonneg (α := ℝ) h]
  obtain ⟨u1, u2, u3, u4, u5⟩ := undamped θ GB (a ^ 2) (b ^ 2) (by positivity) (by positivity)
    fun m hm => by
      have h2p := hGB m hm
      constructor
      · calc (1 / 2 : ℝ) ^ m ≤ (1 / 2) ^ (2 * p) :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) h2p
          _ = a ^ 2 := by rw [hadef, ← pow_mul, mul_comm]
      · calc (1 / 8 : ℝ) ^ m ≤ (1 / 8) ^ (2 * p) :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) h2p
          _ = b ^ 2 := by rw [hbdef, ← pow_mul, mul_comm]
  have f1 : (h : ℝ) * a ^ 2 ≤ A ^ 2 := by
    calc (h : ℝ) * a ^ 2 ≤ A ^ 4 * a ^ 2 := mul_le_mul_of_nonneg_right hBA (by positivity)
      _ = A ^ 2 * (a * A) ^ 2 := by ring
      _ = A ^ 2 := by rw [haA]; ring
  have f2 : (h : ℝ) * b ^ 2 ≤ 1 := by
    calc (h : ℝ) * b ^ 2 ≤ A ^ 4 * b ^ 2 := mul_le_mul_of_nonneg_right hBA (by positivity)
      _ ≤ A ^ 6 * b ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact pow_le_pow_right₀ hA1 (by norm_num)
      _ = (b * A ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hbA]; ring
  refine ⟨u1, u2.trans f1, u3.trans ?_, u4.trans f2, u5.trans ?_⟩
  · calc (h : ℝ) ^ 2 * (a ^ 2) ^ 2 = ((h : ℝ) * a ^ 2) ^ 2 := by ring
      _ ≤ (A ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) f1 2
      _ = A ^ 4 := by ring
  · calc (h : ℝ) ^ 2 * (b ^ 2) ^ 2 = ((h : ℝ) * b ^ 2) ^ 2 := by ring
      _ ≤ 1 ^ 2 := pow_le_pow_left₀ (by positivity) f2 2
      _ = 1 := one_pow 2

/-- The final combination at the dip. -/
lemma combine (n : ℕ) (A P : ℝ) (xp r : T5) (hn : (n : ℝ) = A ^ 4)
    (hP1 : 1 ≤ P) (hP2A : P ^ 2 ≤ A) (hPA : P ^ 4 ≤ A) (hA1 : 1 ≤ A)
    (p1 : |xp.P| ≤ 1) (p2 : |xp.y1| ≤ A ^ 3) (p3 : |xp.z1| ≤ A) (p4 : |xp.z2| ≤ A ^ 2)
    (p5 : crit n xp = 0)
    (r1 : |r.P| ≤ 1) (r2 : |r.y1| ≤ A ^ 2 + 2 * P ^ 2)
    (r3 : |r.y2| ≤ A ^ 4 + 2 * P ^ 2 * A ^ 2 + 4 * P ^ 4)
    (r4 : |r.z1| ≤ 1 + P ^ 2 / 2) (r5 : |r.z2| ≤ 1 + P ^ 2 / 2 + P ^ 4 / 4) :
    Mx n (xp * r) ≤ 32 * P ^ 2 * A ^ 5 := by
  have hA0 : 0 ≤ A := by linarith
  have hA4 : |A ^ 4| ≤ A ^ 4 := le_of_eq (abs_of_nonneg (by positivity))
  have cP : |(xp * r).P| ≤ 1 * 1 := by
    simp only [T5.mul_P]; exact abs_mul_le' p1 r1
  have cy1 : |(xp * r).y1| ≤ 1 * (A ^ 2 + 2 * P ^ 2) + A ^ 3 * 1 := by
    simp only [T5.mul_y1]
    exact (abs_add_le _ _).trans (add_le_add (abs_mul_le' p1 r2) (abs_mul_le' p2 r1))
  have cz1 : |(xp * r).z1| ≤ 1 * (1 + P ^ 2 / 2) + A * 1 := by
    simp only [T5.mul_z1]
    exact (abs_add_le _ _).trans (add_le_add (abs_mul_le' p1 r4) (abs_mul_le' p3 r1))
  have cz2 : |(xp * r).z2| ≤ 1 * (1 + P ^ 2 / 2 + P ^ 4 / 4) + A * (1 + P ^ 2 / 2) + A ^ 2 * 1 := by
    simp only [T5.mul_z2]
    exact (abs_add3_le _ _ _).trans (add_le_add (add_le_add (abs_mul_le' p1 r5)
      (abs_mul_le' p3 r4)) (abs_mul_le' p4 r1))
  have hcr : |crit n r| ≤ A ^ 4 * (1 + P ^ 2 / 2 + P ^ 4 / 4) +
      (A ^ 4 + 2 * P ^ 2 * A ^ 2 + 4 * P ^ 4) := by
    unfold crit; rw [hn]
    exact (abs_sub _ _).trans (add_le_add (abs_mul_le' hA4 r5) r3)
  have hcross : |(n : ℝ) * xp.z1 * r.z1 - xp.y1 * r.y1| ≤
      A ^ 4 * A * (1 + P ^ 2 / 2) + A ^ 3 * (A ^ 2 + 2 * P ^ 2) := by
    rw [hn]
    exact (abs_sub _ _).trans (add_le_add (abs_mul_le' (abs_mul_le' hA4 p3) r4)
      (abs_mul_le' p2 r2))
  have cc : |crit n (xp * r)| ≤ 1 * (A ^ 4 * (1 + P ^ 2 / 2 + P ^ 4 / 4) +
      (A ^ 4 + 2 * P ^ 2 * A ^ 2 + 4 * P ^ 4)) +
      (A ^ 4 * A * (1 + P ^ 2 / 2) + A ^ 3 * (A ^ 2 + 2 * P ^ 2)) := by
    rw [crit_mul, p5, mul_zero, add_zero]
    exact (abs_add_le _ _).trans (add_le_add (abs_mul_le' p1 hcr) hcross)
  have hM := Mx_le n (xp * r) _ _ _ _ _ cP cy1 cz1 cz2 cc
  rw [hn] at hM
  have m1 : A ≤ A ^ 5 := le_self_pow₀ hA1 (by norm_num)
  have m2 : A ^ 2 ≤ A ^ 5 := pow_le_pow_right₀ hA1 (by norm_num)
  have m3 : A ^ 3 ≤ A ^ 5 := pow_le_pow_right₀ hA1 (by norm_num)
  have m4 : A ^ 4 ≤ A ^ 5 := pow_le_pow_right₀ hA1 (by norm_num)
  have m5 : (1 : ℝ) ≤ A ^ 5 := one_le_pow₀ hA1
  have q1 : P ^ 2 * A ^ 4 ≤ A ^ 5 := by
    calc P ^ 2 * A ^ 4 ≤ A * A ^ 4 := mul_le_mul_of_nonneg_right hP2A (by positivity)
      _ = A ^ 5 := by ring
  have q2 : P ^ 4 * A ^ 4 ≤ A ^ 5 := by
    calc P ^ 4 * A ^ 4 ≤ A * A ^ 4 := mul_le_mul_of_nonneg_right hPA (by positivity)
      _ = A ^ 5 := by ring
  have q3 : P ^ 2 * A ^ 2 ≤ A ^ 5 := by
    calc P ^ 2 * A ^ 2 ≤ A * A ^ 2 := mul_le_mul_of_nonneg_right hP2A (by positivity)
      _ = A ^ 3 := by ring
      _ ≤ A ^ 5 := m3
  have q4 : P ^ 2 * A ^ 3 ≤ A ^ 5 := by
    calc P ^ 2 * A ^ 3 ≤ A * A ^ 3 := mul_le_mul_of_nonneg_right hP2A (by positivity)
      _ = A ^ 4 := by ring
      _ ≤ A ^ 5 := m4
  have q5 : P ^ 2 * A ≤ A ^ 5 := by
    calc P ^ 2 * A ≤ A * A := mul_le_mul_of_nonneg_right hP2A hA0
      _ = A ^ 2 := by ring
      _ ≤ A ^ 5 := m2
  have q6 : P ^ 4 ≤ A ^ 5 := hPA.trans m1
  have q7 : P ^ 2 ≤ A ^ 5 := hP2A.trans m1
  have q8 : A ^ 5 ≤ P ^ 2 * A ^ 5 := by
    have : (1 : ℝ) ≤ P ^ 2 := one_le_pow₀ hP1
    nlinarith
  linarith

/-- **Upper bound at the dip**: for `p = pp j` (`j ≥ 1`) and `N = 16^p`, every product of
length `N` that contains `F₁` has `Mx ≤ 32 p² (2^p)^5`. -/
lemma upper_at (j : ℕ) (hj : 1 ≤ j) (G : List ℕ) (hG1 : ∀ m ∈ G, 1 ≤ m)
    (hGs : G.sum ≤ 16 ^ pp j) :
    Mx (16 ^ pp j) ((G.map (Kt θs)).prod) ≤ 32 * (pp j : ℝ) ^ 2 * ((2 : ℝ) ^ pp j) ^ 5 := by
  have hp1 : 1 ≤ pp j := by have := pp_ge j; omega
  have hP256 : (256 : ℝ) ≤ pp j := by exact_mod_cast pp_ge_256 j hj
  have hexp := exp_beats_poly j hj
  have hP1 : (1 : ℝ) ≤ pp j := by linarith
  have hPA : (pp j : ℝ) ^ 4 ≤ (2 : ℝ) ^ pp j := by
    have : (pp j : ℝ) ^ 4 ≤ (pp j : ℝ) ^ 7 := pow_le_pow_right₀ hP1 (by norm_num)
    nlinarith [pow_pos (show (0 : ℝ) < pp j by linarith) 7]
  have hP2A : (pp j : ℝ) ^ 2 ≤ (2 : ℝ) ^ pp j :=
    (pow_le_pow_right₀ hP1 (by norm_num : 2 ≤ 4)).trans hPA
  have hA1 : (1 : ℝ) ≤ (2 : ℝ) ^ pp j := one_le_pow₀ (by norm_num)
  rw [split3 θs G (pp j)]
  obtain ⟨Gp, hGp⟩ : ∃ L, L = G.filter (· = pp j) := ⟨_, rfl⟩
  obtain ⟨G', hG'⟩ : ∃ L, L = G.filter (fun m => ¬ m = pp j) := ⟨_, rfl⟩
  rw [← hGp, ← hG']
  obtain ⟨GS, hGS⟩ : ∃ L, L = G'.filter (· < 2 * pp j) := ⟨_, rfl⟩
  obtain ⟨GB, hGB⟩ : ∃ L, L = G'.filter (fun m => ¬ m < 2 * pp j) := ⟨_, rfl⟩
  rw [← hGS, ← hGB]
  -- the resonant group
  have hGp_eq : Gp = List.replicate Gp.length (pp j) := by
    rw [List.eq_replicate_iff]
    refine ⟨rfl, fun m hm => ?_⟩
    rw [hGp] at hm
    simpa using (List.mem_filter.mp hm).2
  have hcp : Gp.length * pp j ≤ 16 ^ pp j := by
    have h1 : Gp.sum = Gp.length * pp j := by
      conv_lhs => rw [hGp_eq]
      rw [List.sum_replicate_nat]
    have h2 : Gp.sum ≤ G.sum := hGp ▸ sum_filter_le G _
    omega
  have hxp : (Gp.map (Kt θs)).prod = Kt θs (pp j) ^ Gp.length := by
    conv_lhs => rw [hGp_eq]
    rw [List.map_replicate, List.prod_replicate]
  obtain ⟨p1, p2, p3, p4, p5⟩ := resonant_part θs (pp j) Gp.length hcp hp1
  rw [← hxp] at p1 p2 p3 p4 p5
  -- the non-resonant short gaps
  have hS : ∀ m ∈ GS, 1 ≤ m ∧ m < 2 * pp j ∧ m ≠ pp j := by
    intro m hm
    rw [hGS] at hm
    obtain ⟨hm1, hm2⟩ := List.mem_filter.mp hm
    rw [hG'] at hm1
    obtain ⟨hm3, hm4⟩ := List.mem_filter.mp hm1
    simp only [decide_eq_true_eq] at hm2 hm4
    exact ⟨hG1 m hm3, hm2, hm4⟩
  have bS := nonres_part j GS hS
  -- the long gaps
  have hB : ∀ m ∈ GB, 2 * pp j ≤ m := by
    intro m hm
    rw [hGB] at hm
    have := (List.mem_filter.mp hm).2
    simp only [decide_eq_true_eq, not_lt] at this
    exact this
  have hBlen : GB.length * (2 * pp j) ≤ 16 ^ pp j := by
    have h1 : (2 * pp j) * GB.length ≤ GB.sum := sum_ge_length_mul GB (2 * pp j) hB
    have h2 : GB.sum ≤ G'.sum := hGB ▸ sum_filter_le G' _
    have h3 : G'.sum ≤ G.sum := hG' ▸ sum_filter_le G _
    rw [Nat.mul_comm] at h1
    omega
  have bB := big_part θs (pp j) GB hB hBlen hp1
  -- the product of the two non-resonant groups
  have nS := Kab_prod_nonneg θs GS
  have nB := Kab_prod_nonneg θs GB
  have bR := T5_mul_le nS nB bS bB
  have dR : Dom ((GS.map (Kt θs)).prod * (GB.map (Kt θs)).prod)
      ((GS.map (Kab θs)).prod * (GB.map (Kab θs)).prod) :=
    Dom.mul (dom_prod θs GS) (dom_prod θs GB)
  obtain ⟨dR1, dR2, dR3, dR4, dR5⟩ := dR
  obtain ⟨bR1, bR2, bR3, bR4, bR5⟩ := bR
  apply combine (16 ^ pp j) ((2 : ℝ) ^ pp j) (pp j) _ _ (pow_facts (pp j)).2.2 hP1 hP2A hPA hA1
    p1 p2 p3 p4 p5
  · exact dR1.trans (bR1.trans (le_of_eq (by ring)))
  · exact dR2.trans (bR2.trans (le_of_eq (by ring)))
  · exact dR3.trans (bR3.trans (le_of_eq (by ring)))
  · exact dR4.trans (bR4.trans (le_of_eq (by ring)))
  · exact dR5.trans (bR5.trans (le_of_eq (by ring)))

end MF11

namespace MF11

open Filter Topology

/-! ## 12. Products with prescribed gaps, and the lower bounds -/

/-- A word whose reduced form is `mixed a b G`. -/
def mkWord : ℕ → ℕ → List ℕ → List Bool
  | a, b, [] => List.replicate a false ++ (true :: List.replicate (b - 1) false)
  | a, b, m :: G => List.replicate a false ++ (true :: mkWord (m - 1) b G)

lemma st_append_false (a : ℕ) (l : List Bool) :
    (∀ k, st l = .pure k → st (List.replicate a false ++ l) = .pure (a + k)) ∧
    (∀ a' b G, st l = .mixed a' b G →
      st (List.replicate a false ++ l) = .mixed (a + a') b G) := by
  induction a with
  | zero => simp
  | succ a ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨fun k hk => ?_, fun a' b G h => ?_⟩
    · rw [List.replicate_succ, List.cons_append]
      simp only [st, ih1 k hk, St.pure.injEq]
      omega
    · rw [List.replicate_succ, List.cons_append]
      simp only [st, ih2 a' b G h, St.mixed.injEq, and_true]
      omega

lemma st_mkWord (a b : ℕ) (G : List ℕ) (hb : 1 ≤ b) (hG : ∀ m ∈ G, 1 ≤ m) :
    st (mkWord a b G) = .mixed a b G ∧ (mkWord a b G).length = a + b + G.sum := by
  induction G generalizing a with
  | nil =>
    have h0 : st (true :: List.replicate (b - 1) false) = .mixed 0 b [] := by
      simp only [st, st_replicate_false, St.mixed.injEq, and_true, true_and]
      omega
    refine ⟨?_, ?_⟩
    · simp only [mkWord]
      rw [(st_append_false a _).2 0 b [] h0, add_zero]
    · simp only [mkWord, List.length_append, List.length_replicate, List.length_cons,
        List.sum_nil]
      omega
  | cons m G ih =>
    have hm := hG m (List.mem_cons_self ..)
    obtain ⟨ih1, ih2⟩ := ih (m - 1) (fun m' hm' => hG m' (List.mem_cons_of_mem _ hm'))
    have h0 : st (true :: mkWord (m - 1) b G) = .mixed 0 b (m :: G) := by
      simp only [st, ih1, St.mixed.injEq, true_and, List.cons.injEq, and_true]
      omega
    refine ⟨?_, ?_⟩
    · simp only [mkWord]
      rw [(st_append_false a _).2 0 b (m :: G) h0, add_zero]
    · simp only [mkWord, List.length_append, List.length_replicate, List.length_cons, ih2,
        List.sum_cons]
      omega

/-- The critical coordinate of `K_p^c`. -/
lemma crit_pow_lower (θ : ℝ) (p c : ℕ) (n : ℝ) :
    ((c : ℝ) * (c - 1) / 2) * |q θ p| ^ c *
        |n * ((1 / 8 : ℝ) ^ p) ^ 2 - ((1 / 2 : ℝ) ^ p) ^ 2| ≤ |crit n (Kt θ p ^ c)| := by
  obtain ⟨-, -, hy2, -, hz2⟩ := Kt_pow θ p c
  set x := Kt θ p ^ c
  set α : ℝ := (1 / 2 : ℝ) ^ p
  set β : ℝ := (1 / 8 : ℝ) ^ p
  have hα : 0 < α := by positivity
  have hcc : 0 ≤ ((c : ℝ) * (c - 1) / 2) := by
    rcases Nat.eq_zero_or_pos c with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ c := by exact_mod_cast h
      apply div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
  have key : crit n x * α ^ 2 = x.y2 * (n * β ^ 2 - α ^ 2) := by
    unfold crit; linear_combination n * hz2
  have hq1 : |q θ p| ≤ 1 := abs_cos_le_one _
  have hy : ((c : ℝ) * (c - 1) / 2) * |q θ p| ^ c * α ^ 2 ≤ |x.y2| := by
    have e : |q θ p ^ 2 * x.y2| = ((c : ℝ) * (c - 1) / 2) * |q θ p| ^ c * α ^ 2 := by
      rw [hy2, abs_mul, abs_mul, abs_pow, abs_of_nonneg hcc,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ α ^ 2)]
    rw [← e, abs_mul]
    have : |q θ p ^ 2| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hq1
    nlinarith [abs_nonneg x.y2, abs_nonneg (q θ p ^ 2)]
  have e : |crit n x| * α ^ 2 = |x.y2| * |n * β ^ 2 - α ^ 2| := by
    rw [← abs_mul, ← key, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < α ^ 2)]
  have h2 : ((c : ℝ) * (c - 1) / 2) * |q θ p| ^ c * |n * β ^ 2 - α ^ 2| * α ^ 2 ≤
      |crit n x| * α ^ 2 := by
    rw [e]; nlinarith [hy, abs_nonneg (n * β ^ 2 - α ^ 2)]
  exact le_of_mul_le_mul_right h2 (by positivity)

/-- Lower bound for `g(n)` from a product with `c` gaps of length `p`. -/
lemma lower_bound (θ : ℝ) (p c n : ℕ) (hp : 1 ≤ p) (hn : c * p + 1 ≤ n) :
    ((c : ℝ) * (c - 1) / 2) * |q θ p| ^ c *
        |(n : ℝ) * ((1 / 8 : ℝ) ^ p) ^ 2 - ((1 / 2 : ℝ) ^ p) ^ 2| ≤
      2 * growth rowNorm (Amat θ) n := by
  obtain ⟨hst, hlen⟩ := st_mkWord (n - 1 - c * p) 1 (List.replicate c p) le_rfl
    (fun m hm => by rw [(List.mem_replicate.mp hm).2]; exact hp)
  have hlen' : (mkWord (n - 1 - c * p) 1 (List.replicate c p)).length = n := by
    rw [hlen, List.sum_replicate_nat]; omega
  have h1 := crit_le_rowNorm θ _ _ _ _ hst
  rw [hlen', List.map_replicate, List.prod_replicate] at h1
  have h2 := le_growth rowNorm (Amat θ) (mkWord (n - 1 - c * p) 1 (List.replicate c p))
  rw [hlen'] at h2
  have h3 := crit_pow_lower θ p c (n : ℝ)
  linarith

/-! ## 13. The dips (Theorem 1.3) -/

/-- Upper bound for `g` at the length `N = 16^p`. -/
lemma growth_at_dip (j : ℕ) (hj : 1 ≤ j) :
    growth rowNorm (Amat θs) (16 ^ pp j) ≤ 384 * (pp j : ℝ) ^ 2 * ((2 : ℝ) ^ pp j) ^ 5 := by
  have hP1 : (1 : ℝ) ≤ pp j := by exact_mod_cast (by have := pp_ge j; omega : 1 ≤ pp j)
  have hA1 : (1 : ℝ) ≤ (2 : ℝ) ^ pp j := one_le_pow₀ (by norm_num)
  have hN := (pow_facts (pp j)).2.2
  refine growth_le _ _ _ _ fun l hl => ?_
  obtain ⟨hpure, hmixed⟩ := word_upper θs l
  cases hs : st l with
  | pure k =>
    obtain ⟨hk, -⟩ := (reduction θs l).1 k hs
    have h := hpure k hs
    have hk' : (k : ℝ) = ((16 ^ pp j : ℕ) : ℝ) := by rw [hk, hl]
    rw [hk', hN] at h
    have m4 : ((2 : ℝ) ^ pp j) ^ 4 ≤ ((2 : ℝ) ^ pp j) ^ 5 := pow_le_pow_right₀ hA1 (by norm_num)
    have m5 : (1 : ℝ) ≤ ((2 : ℝ) ^ pp j) ^ 5 := one_le_pow₀ hA1
    have hP2 : (1 : ℝ) ≤ (pp j : ℝ) ^ 2 := one_le_pow₀ hP1
    nlinarith
  | mixed a b G =>
    obtain ⟨hb, hG, hsum, -⟩ := (reduction θs l).2 a b G hs
    have h := hmixed a b G hs
    rw [hl] at h hsum
    have hup := upper_at j hj G hG (by omega)
    linarith

set_option maxHeartbeats 1000000 in
/-- **Theorem 1.3 of the paper** (with explicit, weaker constants): for `p = pp j` (`j ≥ 1`) and
`N = 16^p`, `g(N/2) ≥ p·g(N)` and `g(ℓN) ≥ (ℓ-1)·p·g(N)` for every `ℓ ≥ 2`. -/
theorem dips (j : ℕ) (hj : 1 ≤ j) (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    (pp j : ℝ) * growth rowNorm (Amat θs) (16 ^ pp j) ≤
        growth rowNorm (Amat θs) (16 ^ pp j / 2) ∧
      ((ℓ : ℝ) - 1) * pp j * growth rowNorm (Amat θs) (16 ^ pp j) ≤
        growth rowNorm (Amat θs) (ℓ * 16 ^ pp j) := by
  set p := pp j with hpdef
  have hp256 : 256 ≤ p := pp_ge_256 j hj
  obtain ⟨haA, hbA, hN⟩ := pow_facts p
  set A : ℝ := (2 : ℝ) ^ p with hAdef
  set P : ℝ := (p : ℝ) with hPdef
  set a : ℝ := (1 / 2 : ℝ) ^ p with hadef
  set b : ℝ := (1 / 8 : ℝ) ^ p with hbdef
  have hP256 : (256 : ℝ) ≤ P := by rw [hPdef]; exact_mod_cast hp256
  have hA1 : (1 : ℝ) ≤ A := one_le_pow₀ (by norm_num)
  have hA0 : (0 : ℝ) < A := by linarith
  have ha0 : 0 < a := by positivity
  have hexp : (2 : ℝ) ^ 33 * P ^ 7 ≤ A := exp_beats_poly j hj
  have hNb : A ^ 4 * b ^ 2 = a ^ 2 := by
    have : A ^ 4 * b ^ 2 * A ^ 2 = a ^ 2 * A ^ 2 := by
      have e1 : A ^ 4 * b ^ 2 * A ^ 2 = (b * A ^ 3) ^ 2 := by ring
      have e2 : a ^ 2 * A ^ 2 = (a * A) ^ 2 := by ring
      rw [e1, e2, hbA, haA]
    exact mul_right_cancel₀ (by positivity : A ^ 2 ≠ 0) this
  -- the number of gaps: `c₀ = 16^p / (128 p²)`
  have hdvd : 128 * p ^ 2 ∣ 16 ^ p := by
    have hp2 := pp_eq j
    rw [← hpdef] at hp2
    have he := ee_ge j hj
    have h1 : 128 * p ^ 2 = 2 ^ (7 + 2 * ee j) := by
      rw [hp2, ← pow_mul, pow_add, mul_comm (ee j) 2]; norm_num
    have h2 : 16 ^ p = 2 ^ (4 * p) := by rw [pow_mul]; norm_num
    rw [h1, h2]
    apply pow_dvd_pow
    have := lin_le_two_pow (ee j) he
    rw [hp2]
    omega
  obtain ⟨c, hc⟩ := hdvd
  have hcR : (c : ℝ) * (128 * P ^ 2) = A ^ 4 := by
    have : ((16 ^ p : ℕ) : ℝ) = ((128 * p ^ 2 * c : ℕ) : ℝ) := by rw [hc]
    rw [hN] at this; push_cast at this; rw [this]; ring
  have hP1 : (1 : ℝ) ≤ P := by linarith
  have hP47 : P ^ 4 ≤ P ^ 7 := pow_le_pow_right₀ hP1 (by norm_num)
  have hP7 : 0 < P ^ 7 := by positivity
  have hPA : P ^ 4 ≤ A := by nlinarith
  have hP24 : P ^ 2 ≤ P ^ 4 := pow_le_pow_right₀ hP1 (by norm_num)
  have hA14 : A ≤ A ^ 4 := le_self_pow₀ hA1 (by norm_num)
  have hc2 : (2 : ℝ) ≤ c := by
    have h1 : 128 * P ^ 2 * 2 ≤ A ^ 4 := by
      have : (256 : ℝ) ≤ P ^ 2 := by nlinarith
      nlinarith
    by_contra hcon
    have hcon : (c : ℝ) < 2 := not_le.mp hcon
    have : (c : ℝ) * (128 * P ^ 2) < 2 * (128 * P ^ 2) :=
      mul_lt_mul_of_pos_right hcon (by positivity)
    linarith
  -- `|q_p|^c ≥ 1/2`
  have hq : (1 : ℝ) / 2 ≤ |q θs p| ^ c := by
    have hres := q_res j
    rw [← hpdef] at hres
    have h16 : ((16 : ℝ) ^ p) = A ^ 4 := by
      rw [hAdef, ← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h16] at hres
    set δ : ℝ := 36 * P ^ 2 / A ^ 4
    have hδ : (c : ℝ) * δ = 36 / 128 := by
      simp only [δ]
      field_simp
      nlinarith [hcR]
    have hδ0 : 0 ≤ δ := by positivity
    have hδ1 : δ ≤ 1 := by
      have : (c : ℝ) * δ ≤ 1 := by rw [hδ]; norm_num
      nlinarith
    have hb := one_add_mul_le_pow (show -2 ≤ -δ by linarith) c
    have hmono : (1 - δ) ^ c ≤ |q θs p| ^ c :=
      pow_le_pow_left₀ (by linarith) (by linarith) c
    have : (1 : ℝ) + c * (-δ) = 1 - c * δ := by ring
    rw [this, hδ] at hb
    rw [show (1 : ℝ) + -δ = 1 - δ by ring] at hb
    linarith
  -- the upper bound at `N`
  have hup := growth_at_dip j hj
  rw [← hpdef] at hup
  have hg0 : 0 ≤ growth rowNorm (Amat θs) (16 ^ p) := by
    have := (growth_bounds θs (16 ^ p) (Nat.one_le_pow _ _ (by norm_num))).1
    linarith [Nat.cast_nonneg (α := ℝ) (16 ^ p)]
  -- the key inequality `384 P^3 A^5 * 32 ≤ c² a²`
  have hcc : ((c : ℝ) * (c - 1) / 2) ≥ (c : ℝ) ^ 2 / 4 := by nlinarith
  have hC2 : (c : ℝ) ^ 2 * a ^ 2 * (16384 * P ^ 4) = A ^ 6 := by
    have : ((c : ℝ) * (128 * P ^ 2)) ^ 2 * a ^ 2 = A ^ 6 * (a * A) ^ 2 := by
      rw [hcR]; ring
    rw [haA] at this
    linear_combination this
  have hkey : P * (384 * P ^ 2 * A ^ 5) * 32 ≤ (c : ℝ) ^ 2 * a ^ 2 := by
    have hpos : (0 : ℝ) < 16384 * P ^ 4 := by positivity
    refine le_of_mul_le_mul_right ?_ hpos
    rw [hC2]
    have : P * (384 * P ^ 2 * A ^ 5) * 32 * (16384 * P ^ 4) = 201326592 * P ^ 7 * A ^ 5 := by
      ring
    rw [this]
    have h5 : (0 : ℝ) ≤ A ^ 5 := by positivity
    have : 201326592 * P ^ 7 ≤ A := by nlinarith [pow_pos (show (0 : ℝ) < P by linarith) 7]
    calc 201326592 * P ^ 7 * A ^ 5 ≤ A * A ^ 5 := mul_le_mul_of_nonneg_right this h5
      _ = A ^ 6 := by ring
  constructor
  · -- the length `N/2`
    have h2 : 16 ^ p / 2 * 2 = 16 ^ p := Nat.div_mul_cancel (dvd_pow (by norm_num) (by omega))
    have hn : c * p + 1 ≤ 16 ^ p / 2 := by
      have h1 : 128 * p ^ 2 * c = 16 ^ p := hc.symm
      have hc1 : 1 ≤ c := by exact_mod_cast (show (1 : ℝ) ≤ c by linarith)
      have hcp1 : 1 ≤ c * p := Nat.mul_pos hc1 (by omega)
      have hpp : c * p * 4 ≤ 128 * p ^ 2 * c := by
        have : c * p * 4 ≤ c * p * (128 * p) := Nat.mul_le_mul_left _ (by omega)
        calc c * p * 4 ≤ c * p * (128 * p) := this
          _ = 128 * p ^ 2 * c := by ring
      omega
    have hlow := lower_bound θs p c (16 ^ p / 2) (by omega) hn
    have hn2 : ((16 ^ p / 2 : ℕ) : ℝ) = A ^ 4 / 2 := by
      have : ((16 ^ p / 2 * 2 : ℕ) : ℝ) = ((16 ^ p : ℕ) : ℝ) := by rw [h2]
      rw [hN] at this; push_cast at this; linarith
    rw [hn2] at hlow
    have hD : |A ^ 4 / 2 * b ^ 2 - a ^ 2| = a ^ 2 / 2 := by
      rw [show A ^ 4 / 2 * b ^ 2 - a ^ 2 = -(a ^ 2 / 2) by linear_combination hNb / 2,
        abs_neg, abs_of_nonneg (by positivity)]
    rw [← hadef, ← hbdef, hD] at hlow
    have : (c : ℝ) ^ 2 * a ^ 2 / 32 ≤ growth rowNorm (Amat θs) (16 ^ p / 2) := by
      have h3 : (c : ℝ) ^ 2 / 4 * (1 / 2) * (a ^ 2 / 2) ≤
          ((c : ℝ) * (c - 1) / 2) * |q θs p| ^ c * (a ^ 2 / 2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul hcc hq (by norm_num) (by linarith)
      linarith
    have hPg : P * growth rowNorm (Amat θs) (16 ^ p) ≤ P * (384 * P ^ 2 * A ^ 5) :=
      mul_le_mul_of_nonneg_left hup (by linarith)
    linarith
  · -- the length `ℓ N`
    have hℓR : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    have hn : c * p + 1 ≤ ℓ * 16 ^ p := by
      have h1 : 128 * p ^ 2 * c = 16 ^ p := hc.symm
      have hc1 : 1 ≤ c := by exact_mod_cast (show (1 : ℝ) ≤ c by linarith)
      have hcp1 : 1 ≤ c * p := Nat.mul_pos hc1 (by omega)
      have hpp : c * p * 4 ≤ 128 * p ^ 2 * c := by
        have : c * p * 4 ≤ c * p * (128 * p) := Nat.mul_le_mul_left _ (by omega)
        calc c * p * 4 ≤ c * p * (128 * p) := this
          _ = 128 * p ^ 2 * c := by ring
      have : 16 ^ p ≤ ℓ * 16 ^ p := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hlow := lower_bound θs p c (ℓ * 16 ^ p) (by omega) hn
    have hn2 : ((ℓ * 16 ^ p : ℕ) : ℝ) = ℓ * A ^ 4 := by push_cast; rw [← hN]; push_cast; ring
    rw [hn2] at hlow
    have hD : |ℓ * A ^ 4 * b ^ 2 - a ^ 2| = (ℓ - 1) * a ^ 2 := by
      rw [show (ℓ : ℝ) * A ^ 4 * b ^ 2 - a ^ 2 = (ℓ - 1) * a ^ 2 by linear_combination (ℓ : ℝ) * hNb,
        abs_of_nonneg (by nlinarith [sq_nonneg a])]
    rw [← hadef, ← hbdef, hD] at hlow
    have hl1 : (0 : ℝ) ≤ ℓ - 1 := by linarith
    have : ((ℓ : ℝ) - 1) * ((c : ℝ) ^ 2 * a ^ 2 / 16) ≤ growth rowNorm (Amat θs) (ℓ * 16 ^ p) := by
      have h3 : (c : ℝ) ^ 2 / 4 * (1 / 2) * ((ℓ - 1) * a ^ 2) ≤
          ((c : ℝ) * (c - 1) / 2) * |q θs p| ^ c * ((ℓ - 1) * a ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hl1 (sq_nonneg a))
        exact mul_le_mul hcc hq (by norm_num) (by linarith)
      linarith
    have hPg : ((ℓ : ℝ) - 1) * P * growth rowNorm (Amat θs) (16 ^ p) ≤
        ((ℓ : ℝ) - 1) * (P * (384 * P ^ 2 * A ^ 5)) := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hl1
      exact mul_le_mul_of_nonneg_left hup (by linarith)
    have hk2 : ((ℓ : ℝ) - 1) * (P * (384 * P ^ 2 * A ^ 5) * 32) ≤ ((ℓ : ℝ) - 1) * ((c : ℝ) ^ 2 * a ^ 2) :=
      mul_le_mul_of_nonneg_left hkey hl1
    have hca : 0 ≤ (c : ℝ) ^ 2 * a ^ 2 := by positivity
    have hk3 : ((ℓ : ℝ) - 1) * ((c : ℝ) ^ 2 * a ^ 2) ≥ 0 := mul_nonneg hl1 hca
    linarith

end MF11

namespace MF11

open Filter Topology

/-! ## 14. The answer to Problem MF-11 -/

/-- The first property of Problem MF-11 (Varney–Morris, Definition 4.1): `g` is
**weakly increasing**, `∃ c > 0, ∀ k ℓ ≥ 1, g(k + ℓ) ≥ c g(k)`. -/
def WeaklyIncreasing (g : ℕ → ℝ) : Prop :=
  ∃ κ > 0, ∀ k ℓ, 1 ≤ k → 1 ≤ ℓ → κ * g k ≤ g (k + ℓ)

/-- The second property of Problem MF-11 (Varney–Morris, Definition 4.1): `g` is
**weakly upper regularly varying**, `∀ ℓ ≥ 1, ∃ C_ℓ > 0, ∀ k ≥ 1, g(ℓk) ≤ C_ℓ g(k)`. -/
def WeaklyUpperRegularlyVarying (g : ℕ → ℝ) : Prop :=
  ∀ ℓ, 1 ≤ ℓ → ∃ C > 0, ∀ k, 1 ≤ k → g (ℓ * k) ≤ C * g k

lemma tendsto_root_const_mul_pow (c : ℝ) (hc : 0 < c) (k : ℕ) :
    Tendsto (fun n : ℕ => (c * (n : ℝ) ^ k) ^ (1 / (n : ℝ))) atTop (𝓝 1) := by
  have h1 : Tendsto (fun n : ℕ => c ^ (1 / (n : ℝ))) atTop (𝓝 1) := by
    have := Filter.Tendsto.rpow (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c))
      (tendsto_const_div_atTop_nhds_zero_nat 1) (Or.inl hc.ne')
    simpa using this
  have h2 : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / (n : ℝ))) atTop (𝓝 1) :=
    tendsto_rpow_div.comp tendsto_natCast_atTop_atTop
  have h3 := h1.mul (h2.pow k)
  rw [one_pow, mul_one] at h3
  refine h3.congr' (Eventually.of_forall fun n => ?_)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  show c ^ (1 / (n : ℝ)) * ((n : ℝ) ^ (1 / (n : ℝ))) ^ k = (c * (n : ℝ) ^ k) ^ (1 / (n : ℝ))
  rw [Real.mul_rpow hc.le (pow_nonneg hn k)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hn, ← Real.rpow_mul hn]
  congr 1
  ring

/-- If `c₁ n ≤ g(n) ≤ c₂ n³`, then `g(n)^{1/n} → 1`: the joint spectral radius is `1`. -/
lemma tendsto_root_of_bounds (g : ℕ → ℝ) (c₁ c₂ : ℝ) (h1 : 0 < c₁)
    (h : ∀ n, 1 ≤ n → c₁ * n ≤ g n ∧ g n ≤ c₂ * (n : ℝ) ^ 3) :
    Tendsto (fun n : ℕ => g n ^ (1 / (n : ℝ))) atTop (𝓝 1) := by
  have hc2 : 0 < c₂ := by
    have := h 1 le_rfl
    simp at this
    linarith
  have hlow := tendsto_root_const_mul_pow c₁ h1 1
  have hup := tendsto_root_const_mul_pow c₂ hc2 3
  simp only [pow_one] at hlow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact Real.rpow_le_rpow (by positivity) (h n hn).1 (by positivity)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have h0 : 0 ≤ g n := le_trans (by positivity) (h n hn).1
    exact Real.rpow_le_rpow h0 (h n hn).2 (by positivity)

/-- `g` is positive at every length `n ≥ 1`. -/
lemma growth_pos (n : ℕ) (hn : 1 ≤ n) : 0 < growth rowNorm (Amat θs) n := by
  have := (growth_bounds θs n hn).1
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- **Answer to Problem MF-11** (Varney–Morris, Question 1), for the `ℓ^∞` operator norm:
the pair `{F₀(θ⋆), F₁(θ⋆)}` of real `20 × 20` matrices has joint spectral radius one, and its
marginal instability rate sequence is neither weakly increasing nor weakly upper regularly
varying. -/
theorem MF11_answer :
    Tendsto (fun n : ℕ => growth rowNorm (Amat θs) n ^ (1 / (n : ℝ))) atTop (𝓝 1) ∧
    (∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ growth rowNorm (Amat θs) n ∧
      growth rowNorm (Amat θs) n ≤ 40 * (n : ℝ) ^ 3) ∧
    ¬ WeaklyIncreasing (growth rowNorm (Amat θs)) ∧
    ¬ WeaklyUpperRegularlyVarying (growth rowNorm (Amat θs)) := by
  set g := growth rowNorm (Amat θs)
  refine ⟨tendsto_root_of_bounds g 1 40 one_pos fun n hn => ?_, fun n hn => growth_bounds θs n hn,
    ?_, ?_⟩
  · rw [one_mul]; exact growth_bounds θs n hn
  · rintro ⟨κ, hκ, h⟩
    -- choose `j` with `pp j > 1/κ`
    obtain ⟨j, hj1, hjκ⟩ : ∃ j, 1 ≤ j ∧ 1 / κ < pp j := by
      refine ⟨⌈1 / κ⌉₊ + 1, by omega, ?_⟩
      have := lt_pp (⌈1 / κ⌉₊ + 1)
      have h2 : (1 / κ : ℝ) ≤ ⌈1 / κ⌉₊ := Nat.le_ceil _
      have h3 : ((⌈1 / κ⌉₊ + 1 : ℕ) : ℝ) < pp (⌈1 / κ⌉₊ + 1) := by exact_mod_cast this
      push_cast at h3
      linarith
    set N := 16 ^ pp j
    have hN2 : N / 2 + N / 2 = N := by
      have : 2 ∣ N := dvd_pow (by norm_num) (by have := pp_ge j; omega)
      omega
    have hN1 : 1 ≤ N / 2 := by
      have : 4 ≤ pp j := pp_ge j
      have : 16 ≤ N := Nat.le_self_pow (by omega) 16
      omega
    have h1 := h (N / 2) (N / 2) hN1 hN1
    rw [hN2] at h1
    obtain ⟨hdip, -⟩ := dips j hj1 2 le_rfl
    have hgN := growth_pos N (by omega)
    have hκp : 1 < κ * pp j := by
      rw [div_lt_iff₀ hκ] at hjκ; linarith
    nlinarith
  · intro h
    obtain ⟨C, -, hC⟩ := h 2 (by norm_num)
    obtain ⟨j, hj1, hjC⟩ : ∃ j, 1 ≤ j ∧ C < pp j := by
      refine ⟨⌈C⌉₊ + 1, by omega, ?_⟩
      have := lt_pp (⌈C⌉₊ + 1)
      have h2 : C ≤ ⌈C⌉₊ := Nat.le_ceil _
      have h3 : ((⌈C⌉₊ + 1 : ℕ) : ℝ) < pp (⌈C⌉₊ + 1) := by exact_mod_cast this
      push_cast at h3
      linarith
    set N := 16 ^ pp j
    have hN : 1 ≤ N := Nat.one_le_pow _ _ (by norm_num)
    have h1 := hC N hN
    obtain ⟨-, hdip⟩ := dips j hj1 2 le_rfl
    have hgN := growth_pos N hN
    norm_num at hdip
    nlinarith

/-! ### Every other norm -/

lemma growth_le_mul {m : Type*} [Fintype m] [DecidableEq m] (nrm₁ nrm₂ : Matrix m m ℝ → ℝ)
    (k : ℝ) (hk : 0 ≤ k) (h : ∀ A, nrm₁ A ≤ k * nrm₂ A) (A : Bool → Matrix m m ℝ) (n : ℕ) :
    growth nrm₁ A n ≤ k * growth nrm₂ A n := by
  refine growth_le _ _ _ _ fun l hl => ?_
  calc nrm₁ (l.map A).prod ≤ k * nrm₂ (l.map A).prod := h _
    _ ≤ k * growth nrm₂ A l.length := mul_le_mul_of_nonneg_left (le_growth _ _ _) hk
    _ = k * growth nrm₂ A n := by rw [hl]

/-- **Answer to Problem MF-11 for every norm** equivalent to the `ℓ^∞` operator norm (on the
finite-dimensional space of `20 × 20` matrices this is every norm, e.g. the Euclidean operator
norm of the paper). -/
theorem MF11_answer_any_norm (nrm : Matrix ι ι ℝ → ℝ) (c C : ℝ) (hc : 0 < c)
    (h : ∀ A, c * rowNorm A ≤ nrm A ∧ nrm A ≤ C * rowNorm A) :
    Tendsto (fun n : ℕ => growth nrm (Amat θs) n ^ (1 / (n : ℝ))) atTop (𝓝 1) ∧
    (∀ n : ℕ, 1 ≤ n → c * n ≤ growth nrm (Amat θs) n ∧
      growth nrm (Amat θs) n ≤ 40 * C * (n : ℝ) ^ 3) ∧
    ¬ WeaklyIncreasing (growth nrm (Amat θs)) ∧
    ¬ WeaklyUpperRegularlyVarying (growth nrm (Amat θs)) := by
  set g := growth rowNorm (Amat θs)
  set g' := growth nrm (Amat θs)
  have hC : 0 < C := by
    have := h 1
    have h1 : 0 < rowNorm (1 : Matrix ι ι ℝ) := by
      have := abs_mulVec_le (1 : Matrix ι ι ℝ) (fun _ => 1) (fun _ => by simp) (.inl 0)
      have h2 : rowNorm (1 : Matrix ι ι ℝ) ≥ 1 := by simpa using this
      linarith
    nlinarith [this.1, this.2]
  have lo : ∀ n, c * g n ≤ g' n := fun n => by
    have := growth_le_mul rowNorm nrm (1 / c) (by positivity)
      (fun A => by rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc, mul_comm]; exact (h A).1)
      (Amat θs) n
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc, mul_comm] at this
    exact this
  have up : ∀ n, g' n ≤ C * g n := fun n =>
    growth_le_mul nrm rowNorm C hC.le (fun A => (h A).2) (Amat θs) n
  obtain ⟨-, hb, hWI, hWU⟩ := MF11_answer
  have hbd : ∀ n : ℕ, 1 ≤ n → c * n ≤ g' n ∧ g' n ≤ 40 * C * (n : ℝ) ^ 3 := fun n hn =>
    ⟨(mul_le_mul_of_nonneg_left (hb n hn).1 hc.le).trans (lo n),
      calc g' n ≤ C * g n := up n
        _ ≤ C * (40 * (n : ℝ) ^ 3) := mul_le_mul_of_nonneg_left (hb n hn).2 hC.le
        _ = 40 * C * (n : ℝ) ^ 3 := by ring⟩
  refine ⟨tendsto_root_of_bounds g' c (40 * C) hc hbd, hbd, ?_, ?_⟩
  · rintro ⟨κ, hκ, hk⟩
    refine hWI ⟨κ * c / C, by positivity, fun k ℓ hk1 hℓ1 => ?_⟩
    have h1 := hk k ℓ hk1 hℓ1
    have h2 := lo k
    have h3 := up (k + ℓ)
    rw [div_mul_eq_mul_div, div_le_iff₀ hC]
    nlinarith
  · intro hU
    refine hWU fun ℓ hℓ => ?_
    obtain ⟨D, hD0, hD⟩ := hU ℓ hℓ
    refine ⟨D * C / c, div_pos (mul_pos hD0 hC) hc, fun k hk => ?_⟩
    have h1 := hD k hk
    have h2 := lo (ℓ * k)
    have h3 := up k
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    have h4 := mul_le_mul_of_nonneg_left h3 hD0.le
    linarith

end MF11

namespace MF11

open Filter Topology

/-! ## 15. The statement for `20 × 20` matrices and an arbitrary norm -/

lemma card_ι : Fintype.card ι = 20 := by simp

/-- The coordinates of `W = V ⊕ V ⊕ V_Y ⊕ V_Z`, numbered `0, …, 19` as in Appendix A of the
paper: first `e₀, …, e₆` of the first copy of `V`, then those of the second copy, then `e₆, e₅`
of `V_Y`, then `e₁, e₂, e₄, e₅` of `V_Z`. (In the paper these vectors are called `e₁, …, e₇`, and
`V_Y`, `V_Z` are identified with `ℝ²`, `ℝ⁴` by `E_Y = (e₇, e₆)` and `E_Z = (e₂, e₃, e₅, e₆)`.) -/
def eι : ι ≃ Fin 20 :=
  (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (Equiv.refl _)
      (Equiv.sumCongr (Equiv.swap (0 : Fin 2) 1) (Equiv.refl _)))).trans
    ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv)).trans
      ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans
        (finSumFinEquiv.trans (finCongr (by norm_num)))))

lemma prod_reindex {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) (A : Bool → Matrix m m ℝ) (l : List Bool) :
    (l.map fun b => Matrix.reindex e e (A b)).prod = Matrix.reindex e e ((l.map A).prod) := by
  induction l with
  | nil => simp [Matrix.reindex_apply, Matrix.submatrix_one_equiv]
  | cons b l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [ih]
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv]

lemma growth_reindex {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) (nrm : Matrix n n ℝ → ℝ) (A : Bool → Matrix m m ℝ) (k : ℕ) :
    growth nrm (fun b => Matrix.reindex e e (A b)) k =
      growth (fun M => nrm (Matrix.reindex e e M)) A k := by
  unfold growth
  congr 1
  funext w
  rw [prod_reindex]

lemma rowNorm_reindex {m n : Type*} [Fintype m] [Fintype n] [Nonempty m] [Nonempty n]
    (e : m ≃ n) (A : Matrix m m ℝ) : rowNorm (Matrix.reindex e e A) = rowNorm A := by
  unfold rowNorm
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun i _ => ?_
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [Equiv.sum_comp e.symm (fun j => |A (e.symm i) j|)]
    exact Finset.le_sup' (fun i => ∑ j, |A i j|) (Finset.mem_univ _)
  · refine Finset.sup'_le _ _ fun i _ => ?_
    have := Finset.le_sup' (fun i' => ∑ j, |(Matrix.reindex e e A) i' j|) (Finset.mem_univ (e i))
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] at this
    rwa [Equiv.sum_comp e.symm (fun j => |A i j|)] at this

/-- The pair `{F₀(θ⋆), F₁(θ⋆)}` of Theorem 1.3, as two real `20 × 20` matrices in the
coordinates of Appendix A of the paper (`F20 false = F₀(θ⋆)`, `F20 true = F₁(θ⋆)`). -/
def F20 (b : Bool) : Matrix (Fin 20) (Fin 20) ℝ := Matrix.reindex eι eι (Amat θs b)

/-- **The counterexample, for every norm.** For the two real `20 × 20` matrices
`F20 false = F₀(θ⋆)` and `F20 true = F₁(θ⋆)` and every norm `nrm` on the space of `20 × 20`
matrices (it suffices that `c · rowNorm ≤ nrm ≤ C · rowNorm` with `c > 0`, which holds for every
norm), the marginal instability rate sequence `g(n) = max { nrm (F_{b₁} ⋯ F_{bₙ}) : b ∈ {0,1}ⁿ }`
satisfies
* `g(n)^{1/n} → 1`, i.e. the joint spectral radius of the pair is `1`;
* `c n ≤ g(n) ≤ 40 C n³` (so `g` is unbounded but of polynomial growth);
* `g` is **not** weakly increasing;
* `g` is **not** weakly upper regularly varying. -/
theorem MF11_negative_answer
    (nrm : Matrix (Fin 20) (Fin 20) ℝ → ℝ) (c C : ℝ) (hc : 0 < c)
    (h : ∀ M, c * rowNorm M ≤ nrm M ∧ nrm M ≤ C * rowNorm M) :
    Tendsto (fun n : ℕ => growth nrm F20 n ^ (1 / (n : ℝ))) atTop (𝓝 1) ∧
    (∀ n : ℕ, 1 ≤ n → c * n ≤ growth nrm F20 n ∧ growth nrm F20 n ≤ 40 * C * (n : ℝ) ^ 3) ∧
    ¬ WeaklyIncreasing (growth nrm F20) ∧
    ¬ WeaklyUpperRegularlyVarying (growth nrm F20) := by
  have hg : growth nrm F20 = growth (fun M => nrm (Matrix.reindex eι eι M)) (Amat θs) := by
    funext k; exact growth_reindex eι nrm (Amat θs) k
  rw [hg]
  refine MF11_answer_any_norm _ c C hc fun M => ?_
  rw [← rowNorm_reindex eι M]
  exact h _

/-- Reindexing does not change the `ℓ^∞` growth sequence. -/
lemma growth_rowNorm_F20 : growth rowNorm F20 = growth rowNorm (Amat θs) := by
  funext k
  rw [show F20 = fun b => Matrix.reindex eι eι (Amat θs b) from rfl, growth_reindex]
  simp only [rowNorm_reindex]

/-- The same statement for the `ℓ^∞` operator norm itself, together with the explicit bounds
`n ≤ g(n) ≤ 40 n³`. -/
theorem MF11_negative_answer_rowNorm :
    Tendsto (fun n : ℕ => growth rowNorm F20 n ^ (1 / (n : ℝ))) atTop (𝓝 1) ∧
    (∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ growth rowNorm F20 n ∧ growth rowNorm F20 n ≤ 40 * (n : ℝ) ^ 3) ∧
    ¬ WeaklyIncreasing (growth rowNorm F20) ∧
    ¬ WeaklyUpperRegularlyVarying (growth rowNorm F20) := by
  rw [growth_rowNorm_F20]
  exact MF11_answer

end MF11

namespace MF11

open Filter Topology Matrix WithLp
open scoped Matrix.Norms.L2Operator

/-! ## 16. The spectral norm, and Problem MF-11 exactly as posed

From now on `‖A‖` denotes Mathlib's spectral norm `‖A‖₂` of a matrix (the scoped instance
`Matrix.Norms.L2Operator`): the operator norm of `x ↦ A x` on Euclidean space. -/

section Spectral

/-- `‖A‖` is the operator norm of `x ↦ A x` on the Euclidean space `ℝⁿ`. -/
lemma spectral_norm_def {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) :
    ‖A‖ = ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A‖ := rfl

lemma rowNorm_nonneg {n : Type*} [Fintype n] [Nonempty n] (A : Matrix n n ℝ) :
    0 ≤ rowNorm A := by
  obtain ⟨i⟩ := ‹Nonempty n›
  exact (Finset.sum_nonneg fun j _ => abs_nonneg (A i j)).trans
    (Finset.le_sup' (fun i => ∑ j, |A i j|) (Finset.mem_univ i))

lemma abs_mulVec_le_mul {n : Type*} [Fintype n] [Nonempty n] (A : Matrix n n ℝ) (v : n → ℝ)
    (C : ℝ) (hv : ∀ j, |v j| ≤ C) (i : n) : |(A *ᵥ v) i| ≤ rowNorm A * C := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hv i)
  have h1 : |(A *ᵥ v) i| ≤ (∑ j, |A i j|) * C := by
    simp only [Matrix.mulVec, dotProduct]
    calc |∑ j, A i j * v j| ≤ ∑ j, |A i j * v j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |A i j| * C := Finset.sum_le_sum fun j _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hv j) (abs_nonneg _)
      _ = (∑ j, |A i j|) * C := (Finset.sum_mul _ _ _).symm
  exact h1.trans (mul_le_mul_of_nonneg_right
    (Finset.le_sup' (fun i => ∑ j, |A i j|) (Finset.mem_univ i)) hC)

/-- If all coordinates of `x ∈ ℝⁿ` are at most `R` in absolute value, then `‖x‖₂ ≤ n R`. -/
lemma euclid_norm_le {n : Type*} [Fintype n] [Nonempty n] (x : EuclideanSpace ℝ n) (R : ℝ)
    (hx : ∀ i, |x i| ≤ R) :
    ‖x‖ ≤ Fintype.card n * R := by
  obtain ⟨i₀⟩ := ‹Nonempty n›
  have hR : 0 ≤ R := (abs_nonneg _).trans (hx i₀)
  have hcard : (1 : ℝ) ≤ Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hsq : ‖x‖ ^ 2 ≤ (Fintype.card n * R) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have h1 : (Fintype.card n : ℝ) ≤ (Fintype.card n : ℝ) ^ 2 := by nlinarith
    calc ∑ i, x i ^ 2 ≤ ∑ _i : n, R ^ 2 := Finset.sum_le_sum fun i _ => by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hx i) 2
      _ = Fintype.card n * R ^ 2 := by simp
      _ ≤ (Fintype.card n : ℝ) ^ 2 * R ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg R)
      _ = (Fintype.card n * R) ^ 2 := by ring
  exact (sq_le_sq₀ (norm_nonneg x) (mul_nonneg (by positivity) hR)).mp hsq

/-- `rowNorm A ≤ n ‖A‖₂`. -/
lemma rowNorm_le_spectral {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℝ) : rowNorm A ≤ Fintype.card n * ‖A‖ := by
  refine Finset.sup'_le _ _ fun i _ => ?_
  let v : n → ℝ := fun j => if 0 ≤ A i j then 1 else -1
  have hv : ∀ j, |v j| ≤ 1 := fun j => by simp only [v]; split_ifs <;> simp
  have hsum : (A *ᵥ v) i = ∑ j, |A i j| := by
    simp only [Matrix.mulVec, dotProduct, v]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h0
    · rw [mul_one, abs_of_nonneg h0]
    · rw [mul_neg_one, abs_of_neg (not_le.mp h0)]
  have hx : ‖(toLp 2 v : EuclideanSpace ℝ n)‖ ≤ Fintype.card n := by
    have := euclid_norm_le (toLp 2 v : EuclideanSpace ℝ n) 1 hv
    rwa [mul_one] at this
  have h1 : |(A *ᵥ v) i| ≤
      ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A (toLp 2 v : EuclideanSpace ℝ n)‖ := by
    have := PiLp.norm_apply_le
      (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A (toLp 2 v : EuclideanSpace ℝ n)) i
    rw [Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_toLp, Real.norm_eq_abs] at this
    exact this
  calc ∑ j, |A i j| = (A *ᵥ v) i := hsum.symm
    _ ≤ |(A *ᵥ v) i| := le_abs_self _
    _ ≤ ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A (toLp 2 v : EuclideanSpace ℝ n)‖ := h1
    _ ≤ ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A‖ * ‖(toLp 2 v : EuclideanSpace ℝ n)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖A‖ * Fintype.card n := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
    _ = Fintype.card n * ‖A‖ := mul_comm _ _

/-- `‖A‖₂ ≤ n · rowNorm A`. -/
lemma spectral_le_rowNorm {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℝ) : ‖A‖ ≤ Fintype.card n * rowNorm A := by
  rw [spectral_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (Nat.cast_nonneg _) (rowNorm_nonneg A)) fun x => ?_
  have hx : ∀ j, |ofLp x j| ≤ ‖x‖ := fun j => by
    have := PiLp.norm_apply_le x j
    rwa [Real.norm_eq_abs] at this
  have hy : ∀ i, |ofLp (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A x) i| ≤ rowNorm A * ‖x‖ :=
    fun i => by
      rw [Matrix.ofLp_toEuclideanCLM]
      exact abs_mulVec_le_mul A (ofLp x) ‖x‖ hx i
  calc ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A x‖
      ≤ Fintype.card n * (rowNorm A * ‖x‖) := euclid_norm_le _ _ hy
    _ = Fintype.card n * rowNorm A * ‖x‖ := by ring

end Spectral

/-- **The counterexample, with the spectral norm of the problem statement.** For the two real
`20 × 20` matrices `F20 false = F₀(θ⋆)` and `F20 true = F₁(θ⋆)`, the sequence
`g(k) = max { ‖F_{b₁} ⋯ F_{b_k}‖₂ : b ∈ {0,1}^k }` satisfies `g(k)^{1/k} → 1` (joint spectral
radius `1`) and `k/20 ≤ g(k) ≤ 800 k³`, and it is neither weakly increasing nor weakly upper
regularly varying. -/
theorem MF11_negative_answer_spectral :
    Tendsto (fun k : ℕ => growth (fun A => ‖A‖) F20 k ^ (1 / (k : ℝ))) atTop (𝓝 1) ∧
    (∀ k : ℕ, 1 ≤ k → (k : ℝ) / 20 ≤ growth (fun A => ‖A‖) F20 k ∧
      growth (fun A => ‖A‖) F20 k ≤ 800 * (k : ℝ) ^ 3) ∧
    ¬ WeaklyIncreasing (growth (fun A => ‖A‖) F20) ∧
    ¬ WeaklyUpperRegularlyVarying (growth (fun A => ‖A‖) F20) := by
  have hcomp : ∀ M : Matrix (Fin 20) (Fin 20) ℝ,
      1 / 20 * rowNorm M ≤ ‖M‖ ∧ ‖M‖ ≤ 20 * rowNorm M := fun M => by
    have h1 := rowNorm_le_spectral M
    have h2 := spectral_le_rowNorm M
    simp only [Fintype.card_fin, Nat.cast_ofNat] at h1 h2
    constructor <;> linarith
  obtain ⟨h1, hb, h2, h3⟩ :=
    MF11_negative_answer (fun A => ‖A‖) (1 / 20) 20 (by norm_num) hcomp
  refine ⟨h1, fun k hk => ?_, h2, h3⟩
  obtain ⟨hlo, hhi⟩ := hb k hk
  constructor <;> linarith

/-- **Theorem 1.3 of the paper (the dips) for its pair and its Euclidean norm**, with the
factor `p/400` in place of `2^p/(4·10⁵ p⁴)`: for `p = pp j` with `j ≥ 1` (the paper's `p_{j+1}`)
and `N = 16^p`, `g(N/2) ≥ (p/400) g(N)` and `g(ℓN) ≥ ((ℓ-1) p/400) g(N)` for every `ℓ ≥ 2`. -/
theorem dips_spectral (j : ℕ) (hj : 1 ≤ j) (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    (pp j : ℝ) / 400 * growth (fun A => ‖A‖) F20 (16 ^ pp j) ≤
        growth (fun A => ‖A‖) F20 (16 ^ pp j / 2) ∧
      ((ℓ : ℝ) - 1) * pp j / 400 * growth (fun A => ‖A‖) F20 (16 ^ pp j) ≤
        growth (fun A => ‖A‖) F20 (ℓ * 16 ^ pp j) := by
  have hup : ∀ k, growth (fun A => ‖A‖) F20 k ≤ 20 * growth rowNorm (Amat θs) k := fun k => by
    have := growth_le_mul (fun A => ‖A‖) rowNorm 20 (by norm_num) (fun A => by
      have h := spectral_le_rowNorm A
      simp only [Fintype.card_fin, Nat.cast_ofNat] at h
      exact h) F20 k
    rwa [growth_rowNorm_F20] at this
  have hlo : ∀ k, growth rowNorm (Amat θs) k ≤ 20 * growth (fun A => ‖A‖) F20 k := fun k => by
    have := growth_le_mul rowNorm (fun A => ‖A‖) 20 (by norm_num) (fun A => by
      have h := rowNorm_le_spectral A
      simp only [Fintype.card_fin, Nat.cast_ofNat] at h
      exact h) F20 k
    rwa [growth_rowNorm_F20] at this
  obtain ⟨d1, d2⟩ := dips j hj ℓ hℓ
  have hp : (0 : ℝ) ≤ pp j := Nat.cast_nonneg _
  have hl : (0 : ℝ) ≤ (ℓ : ℝ) - 1 := by
    have : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  have h1 := mul_le_mul_of_nonneg_left (hup (16 ^ pp j)) hp
  have h2 := mul_le_mul_of_nonneg_left h1 hl
  have h3 := hlo (16 ^ pp j / 2)
  have h4 := hlo (ℓ * 16 ^ pp j)
  constructor
  · nlinarith
  · nlinarith

/-- The maximal product norm of Problem MF-11 for a set `𝓜` of real `d × d` matrices:
`g_𝓜(k) = sup { ‖A₁ A₂ ⋯ A_k‖₂ : A₁, …, A_k ∈ 𝓜 }`. (The products `A₁ ⋯ A_k` with all
`Aᵢ ∈ 𝓜` are the same as the products `A_k ⋯ A₁` of the problem statement; for a compact set
`𝓜` the supremum is a maximum.) -/
def gM {d : ℕ} (𝓜 : Set (Matrix (Fin d) (Fin d) ℝ)) (k : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ A : Fin k → Matrix (Fin d) (Fin d) ℝ, (∀ i, A i ∈ 𝓜) ∧
    r = ‖(List.ofFn A).prod‖}

/-- For the set `{F false, F true}`, `g_𝓜` is the sequence `growth` used above. -/
lemma gM_range {d : ℕ} (F : Bool → Matrix (Fin d) (Fin d) ℝ) (k : ℕ) :
    gM (Set.range F) k = growth (fun M => ‖M‖) F k := by
  unfold gM growth
  rw [Finset.sup'_eq_csSup_image, Finset.coe_univ, Set.image_univ]
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨A, hA, rfl⟩
    choose w hw using hA
    refine ⟨w, ?_⟩
    have hFw : F ∘ w = A := funext hw
    rw [List.map_ofFn, hFw]
  · rintro ⟨w, rfl⟩
    exact ⟨F ∘ w, fun i => ⟨w i, rfl⟩, by rw [List.map_ofFn]⟩

/-- **Problem MF-11, exactly as posed, has a negative answer.** It is not true that every
compact nonempty set `𝓜` of real square matrices with joint spectral radius
`lim_k g_𝓜(k)^{1/k} = 1` (spectral norm) has a maximal product norm sequence `g_𝓜` that is both
weakly increasing and weakly upper regularly varying. The set `{F₀(θ⋆), F₁(θ⋆)}` of two
`20 × 20` matrices is a counterexample, and it has neither property
(`MF11_negative_answer_spectral`). -/
theorem MF11_answer_is_no :
    ¬ ∀ (d : ℕ) (𝓜 : Set (Matrix (Fin d) (Fin d) ℝ)), IsCompact 𝓜 → 𝓜.Nonempty →
      Tendsto (fun k : ℕ => gM 𝓜 k ^ (1 / (k : ℝ))) atTop (𝓝 1) →
      WeaklyIncreasing (gM 𝓜) ∧ WeaklyUpperRegularlyVarying (gM 𝓜) := by
  intro h
  have hg : gM (Set.range F20) = growth (fun M => ‖M‖) F20 := funext (gM_range F20)
  obtain ⟨h1, -, h2, -⟩ := MF11_negative_answer_spectral
  have h3 := h 20 (Set.range F20) (Set.finite_range F20).isCompact (Set.range_nonempty F20)
    (by rw [hg]; exact h1)
  rw [hg] at h3
  exact h2 h3.1

end MF11

/-! ## Verification: the axioms used by the main statements -/

#print axioms MF11.MF11_answer_is_no
#print axioms MF11.MF11_negative_answer_spectral
#print axioms MF11.dips_spectral
#print axioms MF11.MF11_negative_answer
#print axioms MF11.MF11_negative_answer_rowNorm
#print axioms MF11.dips
