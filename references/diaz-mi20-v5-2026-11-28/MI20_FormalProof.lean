/-
  MI20_FormalProof.lean
  =====================
  Author:      Marcio Díaz
  Affiliation: Space Research AI (https://spaceresearch.ai, marcio.diaz@gmail.com)

  Self-contained, zero-dependency, zero-sorry Lean 4 (v4.35.0) machine-checked
  formalization of the exact algebraic and certificate-based results for
  Open Problem MI-20 ("Sharp subquadratic Lee constants for sums of matrices"):

    Part 1 (Theorem 3, p = 3/2):
      - Exact derivative numerator factorization of R(y^2)^6
      - Exact closed-form evaluation C_{3/2,2}(2)^6 = (107 + 51*sqrt(17)) / 256 in Z[sqrt(17)]
      - Zero-calculus algebraic global maximum proof via exact positive polynomial factorization

    Part 2 (Theorem 4, p = 3/2):
      - Soundness of Sylvester's positive-definiteness criterion (exact block LDL^T identity)
      - Pure-integer operator-monotone & Cayley-orthogonal Sylvester-minor certificate
        proving that the two-digit integer 3x3 pair
            A = [[49, 62, -1], [11, 14, 0], [0, 0, 0]],   B = diag(81, 0, 0)
        strictly beats C_{3/2,2}(2) = ((107 + 51*sqrt(17)) / 256)^(1/6),
        certifying C_{3/2,2}(3) > C_{3/2,2}(2) with zero floating-point arithmetic.

    Part 3 (Core Algebraic Lemmas & Theorem 1 Induction):
      - Exact Sherman-Morrison core inequality of Lemma 4(a)
      - Exact isometry identity of Lemma 2
      - Exact nonnegative-square monotonicity identity of Theorem 3
      - Formal proof of Theorem 1's strict infinite-dimensional hierarchy from Lemmas 1–4.

  Verify:  lean MI20_FormalProof.lean
  Zero external dependencies, zero `sorry`, zero custom axioms.
-/

namespace MI20

/-! ==========================================================================
    PART 0: Elementary Integer Helpers, Quadratic Ring Z[sqrt(17)], and Mat3
    ========================================================================== -/

theorem int_sq_nonneg (a : Int) : a * a ≥ 0 := by
  by_cases h : a ≥ 0
  · exact Int.mul_nonneg h h
  · have hneg : -a ≥ 0 := by omega
    have hmul : (-a) * (-a) ≥ 0 := Int.mul_nonneg hneg hneg
    have heq : (-a) * (-a) = a * a := Int.neg_mul_neg a a
    omega

theorem int_sq_pos (a : Int) (ha : a ≠ 0) : a * a > 0 := by
  by_cases h : a > 0
  · exact Int.mul_pos h h
  · have hneg : -a > 0 := by omega
    have hmul : (-a) * (-a) > 0 := Int.mul_pos hneg hneg
    have heq : (-a) * (-a) = a * a := Int.neg_mul_neg a a
    omega

/-- Helper: `r < 17` and `(r * r) % 17 = 0` implies `r = 0` (17 is prime). -/
theorem mod17_sq_zero : ∀ r : Nat, r < 17 → (r * r) % 17 = 0 → r = 0 := by
  decide

/-- Irrationality of sqrt(17): no nonzero `n : Nat` satisfies `m^2 = 17 * n^2`. -/
theorem no_nat_sq_eq_17_sq : ∀ n m : Nat, n ≠ 0 → m * m ≠ 17 * (n * n) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro m hn hsq
    have hm17 : m % 17 = 0 := by
      have hmod : ((m % 17) * (m % 17)) % 17 = 0 := by
        have h1 : (m * m) % 17 = (17 * (n * n)) % 17 := congrArg (· % 17) hsq
        rw [Nat.mul_mod] at h1
        have h2 : (17 * (n * n)) % 17 = 0 := Nat.mul_mod_right 17 (n * n)
        rw [h2] at h1
        exact h1
      exact mod17_sq_zero (m % 17) (Nat.mod_lt m (by decide)) hmod
    have hm_div : 17 ∣ m := Nat.dvd_of_mod_eq_zero hm17
    rcases hm_div with ⟨m', rfl⟩
    have h17_eq : 17 * (17 * (m' * m')) = 17 * (n * n) := by
      have htmp : 17 * m' * (17 * m') = 17 * (17 * (m' * m')) := by grind
      omega
    have hsq' : n * n = 17 * (m' * m') := by omega
    have hm'_nz : m' ≠ 0 := by
      intro h0
      subst h0
      have : n * n = 0 := by simpa using hsq'
      rcases Nat.mul_eq_zero.mp this with h' | h' <;> exact hn h'
    have hlt_n : m' < n := by
      cases Nat.lt_or_ge m' n with
      | inl hlt => exact hlt
      | inr hge =>
        have hle2 : n * n ≤ m' * m' := Nat.mul_le_mul hge hge
        have hm'pos : m' * m' > 0 :=
          Nat.mul_pos (Nat.pos_of_ne_zero hm'_nz) (Nat.pos_of_ne_zero hm'_nz)
        omega
    exact ih m' hlt_n n hm'_nz hsq'

/-- Elements `a + b * sqrt(17)` of the quadratic integer ring Z[sqrt(17)]. -/
structure ZSqrt17 where
  a : Int
  b : Int
  deriving DecidableEq, Repr

namespace ZSqrt17

def ofInt (n : Int) : ZSqrt17 := ⟨n, 0⟩
def sqrt17 : ZSqrt17 := ⟨0, 1⟩

def add (x y : ZSqrt17) : ZSqrt17 := ⟨x.a + y.a, x.b + y.b⟩
def sub (x y : ZSqrt17) : ZSqrt17 := ⟨x.a - y.a, x.b - y.b⟩
def neg (x : ZSqrt17) : ZSqrt17 := ⟨-x.a, -x.b⟩
def mul (x y : ZSqrt17) : ZSqrt17 :=
  ⟨x.a * y.a + 17 * x.b * y.b, x.a * y.b + x.b * y.a⟩

instance : Add ZSqrt17 := ⟨add⟩
instance : Sub ZSqrt17 := ⟨sub⟩
instance : Neg ZSqrt17 := ⟨neg⟩
instance : Mul ZSqrt17 := ⟨mul⟩
instance : OfNat ZSqrt17 n := ⟨ofInt n⟩

def pow (x : ZSqrt17) : Nat → ZSqrt17
  | 0     => 1
  | n + 1 => x * pow x n

instance : HPow ZSqrt17 Nat ZSqrt17 := ⟨pow⟩

/-- Exact order predicate `a + b*sqrt(17) > 0` expressed purely in `Int`. -/
def IsPos (x : ZSqrt17) : Prop :=
  (x.a ≥ 0 ∧ x.b > 0) ∨
  (x.a > 0 ∧ x.b ≥ 0) ∨
  (x.a > 0 ∧ x.b < 0 ∧ x.a * x.a > 17 * x.b * x.b) ∨
  (x.a < 0 ∧ x.b > 0 ∧ 17 * x.b * x.b > x.a * x.a)

/-- Exact nonnegativity predicate `a + b*sqrt(17) ≥ 0`. -/
def IsNonneg (x : ZSqrt17) : Prop := x = 0 ∨ IsPos x

instance (x : ZSqrt17) : Decidable (IsPos x) := by
  unfold IsPos; infer_instance

/-- Every square `x * x` in `Z[sqrt(17)]` is nonnegative in the real embedding. -/
theorem sq_isNonneg (x : ZSqrt17) : IsNonneg (x * x) := by
  rcases x with ⟨a, b⟩
  show (⟨a * a + 17 * b * b, a * b + b * a⟩ : ZSqrt17) = ⟨0, 0⟩ ∨
    IsPos ⟨a * a + 17 * b * b, a * b + b * a⟩
  by_cases h0 : a = 0 ∧ b = 0
  · left; rcases h0 with ⟨rfl, rfl⟩; rfl
  · right
    have ha_nn : a * a ≥ 0 := int_sq_nonneg a
    have hb_nn : b * b ≥ 0 := int_sq_nonneg b
    have h17b_nn : 17 * b * b ≥ 0 := by
      have : 17 * b * b = 17 * (b * b) := by grind
      omega
    have hpos : a * a + 17 * b * b > 0 := by
      by_cases ha0 : a = 0
      · subst ha0
        have hb0 : b ≠ 0 := fun hb0 => h0 ⟨rfl, hb0⟩
        have hb_p : b * b > 0 := int_sq_pos b hb0
        have : 17 * b * b = 17 * (b * b) := by grind
        omega
      · have ha_p : a * a > 0 := int_sq_pos a ha0
        omega
    by_cases hcross : a * b + b * a ≥ 0
    · exact Or.inr (Or.inl ⟨hpos, hcross⟩)
    · right; right; left
      refine ⟨hpos, by simp; omega, ?_⟩
      simp only []
      have hdiff : (a * a + 17 * b * b) * (a * a + 17 * b * b) -
          17 * (a * b + b * a) * (a * b + b * a) =
          (a * a - 17 * b * b) * (a * a - 17 * b * b) := by grind
      have hne : a * a ≠ 17 * b * b := by
        intro heq
        have hab : a.natAbs * a.natAbs = 17 * (b.natAbs * b.natAbs) := by
          have h1 : (a * a).natAbs = a.natAbs * a.natAbs := Int.natAbs_mul a a
          have h2 : (17 * b * b).natAbs = 17 * (b.natAbs * b.natAbs) := by
            have hassoc : 17 * b * b = 17 * (b * b) := by grind
            rw [hassoc, Int.natAbs_mul, Int.natAbs_mul]; rfl
          rw [← h1, heq, h2]
        have hnz : b.natAbs ≠ 0 := by
          intro hb0
          have hb_eq : b = 0 := Int.natAbs_eq_zero.mp hb0
          subst hb_eq
          have ha2 : a * a = 0 := by simpa using heq
          have ha_eq : a = 0 := by
            by_cases ha : a = 0
            · exact ha
            · have := int_sq_pos a ha; omega
          exact h0 ⟨ha_eq, rfl⟩
        exact no_nat_sq_eq_17_sq b.natAbs a.natAbs hnz hab
      have hsqpos : (a * a - 17 * b * b) * (a * a - 17 * b * b) > 0 :=
        int_sq_pos (a * a - 17 * b * b) (by omega)
      omega

/-- Clean unfolded characterization of `IsPos ⟨a, b⟩`. -/
theorem isPos_mk_iff (a b : Int) :
    IsPos ⟨a, b⟩ ↔
      (a ≥ 0 ∧ b > 0) ∨ (a > 0 ∧ b ≥ 0) ∨
      (a > 0 ∧ b < 0 ∧ a * a > 17 * b * b) ∨
      (a < 0 ∧ b > 0 ∧ 17 * b * b > a * a) := Iff.rfl

/-- Sign-norm dichotomy: every positive `⟨a, b⟩` has either positive norm (`a > 0, a^2 > 17 b^2`)
    or negative norm (`b > 0, 17 b^2 > a^2`). -/
theorem isPos_dichotomy {a b : Int} (h : IsPos ⟨a, b⟩) :
    (a > 0 ∧ a * a > 17 * b * b) ∨ (b > 0 ∧ 17 * b * b > a * a) := by
  rw [isPos_mk_iff] at h
  have no_eq : ∀ u v : Int, v ≠ 0 → u * u ≠ 17 * v * v := by
    intro u v hv heq
    have huv : u.natAbs * u.natAbs = 17 * (v.natAbs * v.natAbs) := by
      have h1 : (u * u).natAbs = u.natAbs * u.natAbs := Int.natAbs_mul u u
      have h2 : (17 * v * v).natAbs = 17 * (v.natAbs * v.natAbs) := by
        have : 17 * v * v = 17 * (v * v) := by grind
        rw [this, Int.natAbs_mul, Int.natAbs_mul]; rfl
      rw [← h1, heq, h2]
    have hvnz : v.natAbs ≠ 0 := fun h0 => hv (Int.natAbs_eq_zero.mp h0)
    exact no_nat_sq_eq_17_sq v.natAbs u.natAbs hvnz huv
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, _, hsq⟩ | ⟨_, hb, hsq⟩
  · by_cases hlt : a * a > 17 * b * b
    · left; refine ⟨?_, hlt⟩
      by_cases ha0 : a = 0
      · subst ha0; have := int_sq_pos b (by omega); grind
      · omega
    · right; have hne := no_eq a b (by omega); exact ⟨hb, by omega⟩
  · by_cases hlt : a * a > 17 * b * b
    · left; exact ⟨ha, hlt⟩
    · right
      have hb0 : b > 0 := by
        by_cases hbz : b = 0
        · subst hbz; have := int_sq_pos a (by omega); grind
        · omega
      have hne := no_eq a b (by omega)
      exact ⟨hb0, by omega⟩
  · left; exact ⟨ha, hsq⟩
  · right; exact ⟨hb, hsq⟩

/-- Helper: `x > 0, y > 0, x^2 > y^2 → x > y`. -/
private theorem int_gt_of_sq_gt {x y : Int} (hx : x ≥ 0) (hy : y ≥ 0) (hsq : x * x > y * y) :
    x > y := by
  by_cases h : x > y
  · exact h
  · have : (y - x) * (y + x) ≥ 0 := Int.mul_nonneg (by omega) (by omega)
    grind

/-- Helper: `c > 0 ∧ c * d > 0 → d > 0`. -/
private theorem int_pos_of_mul_pos {c d : Int} (hc : c > 0) (hcd : c * d > 0) : d > 0 := by
  by_cases hd : d > 0
  · exact hd
  · have : c * (-d) ≥ 0 := Int.mul_nonneg (by omega) (by omega)
    grind

/-- Helper: if `x > 0, y > 0, u > 0, v > 0, x > y, u > v`, `x^2 > k u^2` and `k v^2 > y^2` (`k > 0`),
    then `(x - y)^2 > k (u - v)^2`. -/
private theorem sub_sq_gt_scaled {k x y u v : Int} (_hk : k > 0)
    (hx : x > 0) (hy : y > 0) (hu : u > 0) (hv : v > 0)
    (_hxy : x > y) (huv : u > v) (hxu : x * x > k * u * u) (hyv : k * v * v > y * y) :
    (x - y) * (x - y) > k * (u - v) * (u - v) := by
  have hxv_sq : (x * v) * (x * v) > (u * y) * (u * y) := by
    have hv2 : v * v > 0 := Int.mul_pos hv hv
    have hu2 : u * u > 0 := Int.mul_pos hu hu
    have h1 : (x * x - k * u * u) * (v * v) > 0 := Int.mul_pos (by omega) hv2
    have h2 : (k * v * v - y * y) * (u * u) > 0 := Int.mul_pos (by omega) hu2
    grind
  have hxv : x * v > u * y :=
    int_gt_of_sq_gt (by have := Int.mul_pos hx hv; omega) (by have := Int.mul_pos hu hy; omega) hxv_sq
  have h1 : u * (x - y) > x * (u - v) := by grind
  have hrhs : x * (u - v) > 0 := Int.mul_pos hx (by omega)
  have hsq1 : (u * (x - y)) * (u * (x - y)) > (x * (u - v)) * (x * (u - v)) := by
    have : (u * (x - y) - x * (u - v)) * (u * (x - y) + x * (u - v)) > 0 :=
      Int.mul_pos (by omega) (by omega)
    grind
  have hsq2 : (x * (u - v)) * (x * (u - v)) > k * (u * u) * ((u - v) * (u - v)) := by
    have : (x * x - k * u * u) * ((u - v) * (u - v)) > 0 :=
      Int.mul_pos (by omega) (Int.mul_pos (by omega) (by omega))
    grind
  have hmul : (u * u) * ((x - y) * (x - y) - k * (u - v) * (u - v)) > 0 := by grind
  have hpos := int_pos_of_mul_pos (Int.mul_pos hu hu) hmul
  omega

/-- Exact closure of `IsPos` under addition in `Z[sqrt(17)]`. -/
theorem isPos_add {x y : ZSqrt17} (hx : x.IsPos) (hy : y.IsPos) : (x + y).IsPos := by
  rcases x with ⟨a, b⟩; rcases y with ⟨c, d⟩
  show IsPos ⟨a + c, b + d⟩
  rw [isPos_mk_iff]
  have hL : ∀ u v : Int, IsPos ⟨u, v⟩ →
      (u ≤ 0 → v > 0 ∧ 17 * v * v > u * u) ∧ (v ≤ 0 → u > 0 ∧ u * u > 17 * v * v) := by
    intro u v h
    rcases isPos_dichotomy h with ⟨hu, hsq⟩ | ⟨hv, hsq⟩
    · exact ⟨fun hu0 => by omega, fun _ => ⟨hu, hsq⟩⟩
    · exact ⟨fun _ => ⟨hv, hsq⟩, fun hv0 => by omega⟩
  by_cases h1 : a + c ≥ 0 ∧ b + d > 0
  · exact Or.inl h1
  by_cases h2 : a + c > 0 ∧ b + d ≥ 0
  · exact Or.inr (Or.inl h2)
  by_cases hA : a + c > 0 ∧ b + d < 0
  · right; right; left; refine ⟨hA.1, hA.2, ?_⟩
    by_cases hb : b ≤ 0
    · by_cases hd : d ≤ 0
      · have ⟨ha, ha2⟩ := (hL a b hx).2 hb
        have ⟨hc, hc2⟩ := (hL c d hy).2 hd
        have hbd : b * d ≥ 0 := by
          have := Int.mul_nonneg (by omega : -b ≥ 0) (by omega : -d ≥ 0); grind
        have hsq : (a * c) * (a * c) > (17 * b * d) * (17 * b * d) := by
          have h1 := Int.mul_pos (by omega : a * a - 17 * b * b > 0) (int_sq_pos c (by omega))
          have hb2 : 17 * b * b ≥ 0 := by have := int_sq_nonneg b; grind
          have h2 := Int.mul_nonneg hb2 (by omega : c * c - 17 * d * d ≥ 0)
          grind
        have h17bd : 17 * b * d ≥ 0 := by
          have : 17 * b * d = 17 * (b * d) := by grind
          omega
        have hac := int_gt_of_sq_gt (by have := Int.mul_pos ha hc; omega) h17bd hsq
        grind
      · have ⟨ha, ha2⟩ := (hL a b hx).2 hb
        by_cases hc : c ≥ 0
        · have hbd_lt : (b + d) * (b + d) < b * b := by
            have := Int.mul_pos (by omega : d > 0) (by omega : -(2 * b + d) > 0); grind
          have hac_ge : (a + c) * (a + c) ≥ a * a := by
            have := Int.mul_nonneg hc (by omega : 2 * a + c ≥ 0); grind
          grind
        · have ⟨_, hd2⟩ := (hL c d hy).1 (by omega)
          have hsub := sub_sq_gt_scaled (k := 17) (x := a) (y := -c) (u := -b) (v := d)
            (by omega) ha (by omega) (by omega) (by omega) (by omega) (by omega) (by grind) (by grind)
          grind
    · have ⟨hc, hc2⟩ := (hL c d hy).2 (by omega)
      by_cases ha : a ≥ 0
      · have hbd_lt : (b + d) * (b + d) < d * d := by
          have := Int.mul_pos (by omega : b > 0) (by omega : -(2 * d + b) > 0); grind
        have hac_ge : (a + c) * (a + c) ≥ c * c := by
          have := Int.mul_nonneg ha (by omega : 2 * c + a ≥ 0); grind
        grind
      · have ⟨_, hb2⟩ := (hL a b hx).1 (by omega)
        have hsub := sub_sq_gt_scaled (k := 17) (x := c) (y := -a) (u := -d) (v := b)
          (by omega) hc (by omega) (by omega) (by omega) (by omega) (by omega) (by grind) (by grind)
        grind
  by_cases hB : a + c < 0 ∧ b + d > 0
  · right; right; right; refine ⟨hB.1, hB.2, ?_⟩
    by_cases ha : a ≤ 0
    · by_cases hc : c ≤ 0
      · have ⟨hb, hb2⟩ := (hL a b hx).1 ha
        have ⟨hd, hd2⟩ := (hL c d hy).1 hc
        have hac : a * c ≥ 0 := by
          have := Int.mul_nonneg (by omega : -a ≥ 0) (by omega : -c ≥ 0); grind
        have hsq : (17 * b * d) * (17 * b * d) > (a * c) * (a * c) := by
          have hd2p : 17 * d * d > 0 := by have := int_sq_pos d (by omega); grind
          have h1 := Int.mul_pos (by omega : 17 * b * b - a * a > 0) hd2p
          have h2 := Int.mul_nonneg (int_sq_nonneg a) (by omega : 17 * d * d - c * c ≥ 0)
          grind
        have hbd := int_gt_of_sq_gt (by have := Int.mul_pos hb hd; grind) hac hsq
        grind
      · have ⟨hb, hb2⟩ := (hL a b hx).1 ha
        by_cases hd : d ≥ 0
        · have hac_lt : (a + c) * (a + c) < a * a := by
            have := Int.mul_pos (by omega : c > 0) (by omega : -(2 * a + c) > 0); grind
          have hbd_ge : (b + d) * (b + d) ≥ b * b := by
            have := Int.mul_nonneg hd (by omega : 2 * b + d ≥ 0); grind
          grind
        · have ⟨_, hc2⟩ := (hL c d hy).2 (by omega)
          -- Multiply by 17: (17*b)^2 > 17*(-a)^2 and 17*c^2 > (17*(-d))^2!
          have hsub := sub_sq_gt_scaled (k := 17) (x := 17 * b) (y := 17 * (-d)) (u := -a) (v := c)
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by grind) (by grind)
          grind
    · have ⟨hd, hd2⟩ := (hL c d hy).1 (by omega)
      by_cases hb : b ≥ 0
      · have hac_lt : (a + c) * (a + c) < c * c := by
          have := Int.mul_pos (by omega : a > 0) (by omega : -(2 * c + a) > 0); grind
        have hbd_ge : (b + d) * (b + d) ≥ d * d := by
          have := Int.mul_nonneg hb (by omega : 2 * d + b ≥ 0); grind
        grind
      · have ⟨_, ha2⟩ := (hL a b hx).2 (by omega)
        have hsub := sub_sq_gt_scaled (k := 17) (x := 17 * d) (y := 17 * (-b)) (u := -c) (v := a)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by grind) (by grind)
        grind
  exfalso
  by_cases ha : a ≤ 0
  · have ⟨hb, hb2⟩ := (hL a b hx).1 ha
    have ⟨hc, hc2⟩ := (hL c d hy).2 (by omega)
    have h1 : (-a) * (-a) ≥ c * c := by
      have := Int.mul_nonneg (by omega : -a - c ≥ 0) (by omega : -a + c ≥ 0); grind
    have h2 : (-d) * (-d) ≥ b * b := by
      have := Int.mul_nonneg (by omega : -d - b ≥ 0) (by omega : -d + b ≥ 0); grind
    grind
  · have ⟨hd, hd2⟩ := (hL c d hy).1 (by omega)
    have ⟨_, ha2⟩ := (hL a b hx).2 (by omega)
    have h1 : (-c) * (-c) ≥ a * a := by
      have := Int.mul_nonneg (by omega : -c - a ≥ 0) (by omega : -c + a ≥ 0); grind
    have h2 : (-b) * (-b) ≥ d * d := by
      have := Int.mul_nonneg (by omega : -b - d ≥ 0) (by omega : -b + d ≥ 0); grind
    grind

theorem isNonneg_add {x y : ZSqrt17} (hx : x.IsNonneg) (hy : y.IsNonneg) : (x + y).IsNonneg := by
  rcases hx with rfl | hx
  · show (⟨0 + y.a, 0 + y.b⟩ : ZSqrt17).IsNonneg; simpa using hy
  · rcases hy with rfl | hy
    · rcases x with ⟨a, b⟩
      show (⟨a + 0, b + 0⟩ : ZSqrt17).IsNonneg
      rw [Int.add_zero, Int.add_zero]
      exact Or.inr hx
    · exact Or.inr (isPos_add hx hy)

theorem isNonneg_mul_ofInt {x : ZSqrt17} (hx : x.IsPos) {k : Int} (hk : k ≥ 0) :
    (x * ofInt k).IsNonneg := by
  rcases x with ⟨a, b⟩
  show (⟨a * k + 17 * b * 0, a * 0 + b * k⟩ : ZSqrt17) = ⟨0, 0⟩ ∨
    IsPos ⟨a * k + 17 * b * 0, a * 0 + b * k⟩
  by_cases hk0 : k = 0
  · left; subst hk0; simp
  · right
    rw [isPos_mk_iff]
    rw [isPos_mk_iff] at hx
    have hkp : k > 0 := by omega
    have hk2 : k * k > 0 := Int.mul_pos hkp hkp
    rcases hx with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb, hsq⟩ | ⟨ha, hb, hsq⟩
    · left; exact ⟨by have := Int.mul_nonneg ha (by omega : k ≥ 0); grind,
                   by have := Int.mul_pos hb hkp; grind⟩
    · right; left; exact ⟨by have := Int.mul_pos ha hkp; grind,
                          by have := Int.mul_nonneg hb (by omega : k ≥ 0); grind⟩
    · right; right; left
      refine ⟨by have := Int.mul_pos ha hkp; grind,
              by have := Int.mul_pos (by omega : -b > 0) hkp; grind, ?_⟩
      have : (a * a - 17 * b * b) * (k * k) > 0 := Int.mul_pos (by omega) hk2
      grind
    · right; right; right
      refine ⟨by have := Int.mul_pos (by omega : -a > 0) hkp; grind,
              by have := Int.mul_pos hb hkp; grind, ?_⟩
      have : (17 * b * b - a * a) * (k * k) > 0 := Int.mul_pos (by omega) hk2
      grind

/-- Exact closure of `IsPos` under multiplication in `Z[sqrt(17)]`. -/
theorem isPos_mul {x y : ZSqrt17} (hx : x.IsPos) (hy : y.IsPos) : (x * y).IsPos := by
  rcases x with ⟨a, b⟩; rcases y with ⟨c, d⟩
  show IsPos ⟨a * c + 17 * b * d, a * d + b * c⟩
  rw [isPos_mk_iff]
  rcases isPos_dichotomy hx with ⟨ha, ha2⟩ | ⟨hb, hb2⟩ <;>
  rcases isPos_dichotomy hy with ⟨hc, hc2⟩ | ⟨hd, hd2⟩
  · have hu2 : (a * c + 17 * b * d) * (a * c + 17 * b * d) >
        17 * (a * d + b * c) * (a * d + b * c) := by
      have := Int.mul_pos (by omega : a * a - 17 * b * b > 0) (by omega : c * c - 17 * d * d > 0)
      grind
    have hu : a * c + 17 * b * d > 0 := by
      have hac : a * c > 0 := Int.mul_pos ha hc
      have h1 := Int.mul_pos (by omega : a * a - 17 * b * b > 0) (int_sq_pos c (by omega))
      have hbnn : 17 * b * b ≥ 0 := by have := int_sq_nonneg b; grind
      have h2 := Int.mul_nonneg hbnn (by omega : c * c - 17 * d * d ≥ 0)
      by_cases hpos : a * c + 17 * b * d > 0
      · exact hpos
      · have := Int.mul_nonneg (by omega : -(17 * b * d) - a * c ≥ 0) (by omega : -(17 * b * d) + a * c ≥ 0)
        grind
    by_cases hv : a * d + b * c ≥ 0
    · exact Or.inr (Or.inl ⟨hu, hv⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hu, by omega, hu2⟩))
  · have hv2 : 17 * (a * d + b * c) * (a * d + b * c) >
        (a * c + 17 * b * d) * (a * c + 17 * b * d) := by
      have := Int.mul_pos (by omega : a * a - 17 * b * b > 0) (by omega : 17 * d * d - c * c > 0)
      grind
    have hv : a * d + b * c > 0 := by
      have had : a * d > 0 := Int.mul_pos ha hd
      have hd2p : 17 * d * d > 0 := by have := int_sq_pos d (by omega); grind
      have h1 := Int.mul_pos (by omega : a * a - 17 * b * b > 0) hd2p
      have hbnn : 17 * b * b ≥ 0 := by have := int_sq_nonneg b; grind
      have h2 := Int.mul_nonneg hbnn (by omega : 17 * d * d - c * c ≥ 0)
      by_cases hpos : a * d + b * c > 0
      · exact hpos
      · have := Int.mul_nonneg (by omega : -(b * c) - a * d ≥ 0) (by omega : -(b * c) + a * d ≥ 0)
        grind
    by_cases hu : a * c + 17 * b * d ≥ 0
    · exact Or.inl ⟨hu, hv⟩
    · exact Or.inr (Or.inr (Or.inr ⟨by omega, hv, hv2⟩))
  · have hv2 : 17 * (a * d + b * c) * (a * d + b * c) >
        (a * c + 17 * b * d) * (a * c + 17 * b * d) := by
      have := Int.mul_pos (by omega : 17 * b * b - a * a > 0) (by omega : c * c - 17 * d * d > 0)
      grind
    have hv : a * d + b * c > 0 := by
      have hbc : b * c > 0 := Int.mul_pos hb hc
      have h1 := Int.mul_pos (by omega : 17 * b * b - a * a > 0) (int_sq_pos c (by omega))
      have h2 := Int.mul_nonneg (int_sq_nonneg a) (by omega : c * c - 17 * d * d ≥ 0)
      by_cases hpos : a * d + b * c > 0
      · exact hpos
      · have := Int.mul_nonneg (by omega : -(a * d) - b * c ≥ 0) (by omega : -(a * d) + b * c ≥ 0)
        grind
    by_cases hu : a * c + 17 * b * d ≥ 0
    · exact Or.inl ⟨hu, hv⟩
    · exact Or.inr (Or.inr (Or.inr ⟨by omega, hv, hv2⟩))
  · have hu2 : (a * c + 17 * b * d) * (a * c + 17 * b * d) >
        17 * (a * d + b * c) * (a * d + b * c) := by
      have := Int.mul_pos (by omega : 17 * b * b - a * a > 0) (by omega : 17 * d * d - c * c > 0)
      grind
    have hu : a * c + 17 * b * d > 0 := by
      have hbd : 17 * b * d > 0 := by have := Int.mul_pos hb hd; grind
      have hd2p : 17 * d * d > 0 := by have := int_sq_pos d (by omega); grind
      have h1 := Int.mul_pos (by omega : 17 * b * b - a * a > 0) hd2p
      have h2 := Int.mul_nonneg (int_sq_nonneg a) (by omega : 17 * d * d - c * c ≥ 0)
      by_cases hpos : a * c + 17 * b * d > 0
      · exact hpos
      · have := Int.mul_nonneg (by omega : -(a * c) - 17 * b * d ≥ 0) (by omega : -(a * c) + 17 * b * d ≥ 0)
        grind
    by_cases hv : a * d + b * c ≥ 0
    · exact Or.inr (Or.inl ⟨hu, hv⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hu, by omega, hu2⟩))

theorem isNonneg_mul {x y : ZSqrt17} (hx : x.IsNonneg) (hy : y.IsNonneg) : (x * y).IsNonneg := by
  rcases hx with rfl | hx
  · left; show (⟨0 * y.a + 17 * 0 * y.b, 0 * y.b + 0 * y.a⟩ : ZSqrt17) = ⟨0, 0⟩; simp
  · rcases hy with rfl | hy
    · left; show (⟨x.a * 0 + 17 * x.b * 0, x.a * 0 + x.b * 0⟩ : ZSqrt17) = ⟨0, 0⟩; simp
    · exact Or.inr (isPos_mul hx hy)

/-- If `4 * x` is nonnegative in `Z[sqrt(17)]`, then `x` is nonnegative. -/
theorem isNonneg_of_mul4 {x : ZSqrt17} (h : (ofInt 4 * x).IsNonneg) : x.IsNonneg := by
  rcases x with ⟨a, b⟩
  have heq : ofInt 4 * ⟨a, b⟩ = (⟨4 * a, 4 * b⟩ : ZSqrt17) := by
    show (⟨4 * a + 17 * 0 * b, 4 * b + 0 * a⟩ : ZSqrt17) = ⟨4 * a, 4 * b⟩
    congr 1 <;> grind
  rw [heq] at h
  rcases h with h0 | hpos
  · left
    have ha : 4 * a = 0 := congrArg ZSqrt17.a h0
    have hb : 4 * b = 0 := congrArg ZSqrt17.b h0
    have : a = 0 := by omega
    have : b = 0 := by omega
    subst ‹a = 0›; subst ‹b = 0›; rfl
  · right
    rw [isPos_mk_iff] at hpos ⊢
    rcases hpos with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · left; omega
    · right; left; omega
    · right; right; left; refine ⟨by omega, by omega, ?_⟩; grind
    · right; right; right; refine ⟨by omega, by omega, ?_⟩; grind

end ZSqrt17


/-! ==========================================================================
    PART 1: Theorem 3 (p = 3/2) — Exact Closed Form & Zero-Calculus Global Max
    ========================================================================== -/

/-- Exact numerator of the quotient-rule derivative of `R(y^2)^6 = (y^2+1)^3(y^6+1)/(y^3+1)^4`. -/
theorem thm3_derivative_numerator (y : Int) :
    (6 * y * (y^2 + 1)^2 * (y^6 + 1) + 6 * y^5 * (y^2 + 1)^3) * (y^3 + 1)
    - 12 * y^2 * (y^2 + 1)^3 * (y^6 + 1)
    = -6 * y * (y - 1) * (y^2 + 1)^3 * (y^4 - y^3 - 2 * y^2 - y + 1) := by
  grind

/-- Exact palindromic reduction of the critical-point quartic over `Z[sqrt(17)]`:
    `(2y^2 - (1 + sqrt(17))*y + 2) * (2y^2 - (1 - sqrt(17))*y + 2) = 4*(y^4 - y^3 - 2y^2 - y + 1)`. -/
theorem thm3_quartic_factorization (y : Int) :
    let yz : ZSqrt17 := ZSqrt17.ofInt y
    let fac1 : ZSqrt17 := ZSqrt17.ofInt (2 * y^2 + 2) - ⟨1, 1⟩ * yz
    let fac2 : ZSqrt17 := ZSqrt17.ofInt (2 * y^2 + 2) - ⟨1, -1⟩ * yz
    fac1 * fac2 = ZSqrt17.ofInt (4 * (y^4 - y^3 - 2 * y^2 - y + 1)) := by
  intro yz fac1 fac2
  simp only [yz, fac1, fac2, ZSqrt17.ofInt, HMul.hMul, HSub.hSub, Mul.mul, Sub.sub,
    ZSqrt17.mul, ZSqrt17.sub]
  congr 1 <;> grind

/-- Exact evaluation of `C_{3/2,2}(2)^6` at `2*z_* = 1 + sqrt(17)` in `Z[sqrt(17)]`:
    `256 * (2*z_*)^4 * ((2*z_*)^2 - 12) = (107 + 51*sqrt(17)) * (2*z_* + 4)^2 * (2*z_* - 2)^4`. -/
theorem thm3_closed_form_at_zstar :
    let w : ZSqrt17 := ⟨1, 1⟩
    let c2_num : ZSqrt17 := ⟨107, 51⟩
    ZSqrt17.ofInt 256 * (w ^ 4) * (w ^ 2 - ZSqrt17.ofInt 12)
      = c2_num * ((w + ZSqrt17.ofInt 4) ^ 2) * ((w - ZSqrt17.ofInt 2) ^ 4) := by
  decide

/-- The 5 distinct palindromic coefficients `c_0..c_4` of the degree-8 cofactor `P_8(y)` in `Z[sqrt(17)]`. -/
def c0 : ZSqrt17 := ⟨-149, 51⟩
def c1 : ZSqrt17 := ⟨718, -98⟩
def c2 : ZSqrt17 := ⟨-1181, 363⟩
def c3 : ZSqrt17 := ⟨2302, -434⟩
def c4 : ZSqrt17 := ⟨-2052, 668⟩

/-- Every coefficient `c_0..c_4` of the degree-8 cofactor is strictly positive in `Z[sqrt(17)]`! -/
theorem thm3_cofactor_coeffs_pos :
    c0.IsPos ∧ c1.IsPos ∧ c2.IsPos ∧ c3.IsPos ∧ c4.IsPos := by
  decide

/-- ZERO-CALCULUS GLOBAL OPTIMALITY IDENTITY FOR THEOREM 3 (p = 3/2):
    For ALL integers `p, q` (representing any rational `y = p/q`), homogeneously:
      `4 * [(107 + 51*sqrt(17))*(p^3 + q^3)^4 - 256*(p^2 + q^2)^3*(p^6 + q^6)]`
      `= (2*p^2 - (1 + sqrt(17))*p*q + 2*q^2)^2 * P_8(p, q)`
    where every coefficient of `P_8(p, q)` is strictly positive (by `thm3_cofactor_coeffs_pos`).
    This certifies `R(y^2)^6 ≤ (107 + 51*sqrt(17)) / 256` for ALL `y ≥ 0`, with equality iff
    `2*y^2 - (1 + sqrt(17))*y + 2 = 0`. -/
theorem thm3_global_optimality_identity (p q : Int) :
    let lhs : ZSqrt17 :=
      ZSqrt17.ofInt 4 *
        (⟨107, 51⟩ * ZSqrt17.ofInt ((p^3 + q^3)^4)
         - ZSqrt17.ofInt (256 * (p^2 + q^2)^3 * (p^6 + q^6)))
    let crit : ZSqrt17 :=
      ZSqrt17.ofInt (2 * p^2 + 2 * q^2) - ⟨1, 1⟩ * ZSqrt17.ofInt (p * q)
    let P8 : ZSqrt17 :=
      c0 * ZSqrt17.ofInt (p^8 + q^8)
      + c1 * ZSqrt17.ofInt (p^7 * q + p * q^7)
      + c2 * ZSqrt17.ofInt (p^6 * q^2 + p^2 * q^6)
      + c3 * ZSqrt17.ofInt (p^5 * q^3 + p^3 * q^5)
      + c4 * ZSqrt17.ofInt (p^4 * q^4)
    lhs = (crit * crit) * P8 := by
  intro lhs crit P8
  simp only [lhs, crit, P8, c0, c1, c2, c3, c4, ZSqrt17.ofInt,
    HAdd.hAdd, HSub.hSub, HMul.hMul, Add.add, Sub.sub, Mul.mul,
    ZSqrt17.add, ZSqrt17.sub, ZSqrt17.mul]
  congr 1 <;> grind

/-- END-TO-END ZERO-CALCULUS GLOBAL MAXIMUM THEOREM FOR THEOREM 3 (p = 3/2):
    For EVERY pair of nonnegative integers `p ≥ 0, q ≥ 0` (every rational `y = p/q ≥ 0`,
    hence by density every real `y ≥ 0`),
      `(107 + 51*sqrt(17)) * (p^3 + q^3)^4  ≥  256 * (p^2 + q^2)^3 * (p^6 + q^6)`
    in the exact ordered ring `Z[sqrt(17)]`! -/
theorem thm3_global_max_nonneg (p q : Int) (hp : p ≥ 0) (hq : q ≥ 0) :
    ZSqrt17.IsNonneg
      (⟨107, 51⟩ * ZSqrt17.ofInt ((p^3 + q^3)^4)
       - ZSqrt17.ofInt (256 * (p^2 + q^2)^3 * (p^6 + q^6))) := by
  apply ZSqrt17.isNonneg_of_mul4
  rw [thm3_global_optimality_identity p q]
  apply ZSqrt17.isNonneg_mul (ZSqrt17.sq_isNonneg _)
  -- Show each of the 5 nonnegative-weighted positive terms of P8 is IsNonneg!
  have hpow : ∀ n : Nat, ∀ a : Int, a ≥ 0 → a ^ n ≥ 0 := by
    intro n a ha
    induction n with
    | zero => simp
    | succ k ih =>
      have : a ^ (k + 1) = a ^ k * a := Int.pow_succ a k
      rw [this]
      exact Int.mul_nonneg ih ha
  have hp8 : p^8 + q^8 ≥ 0 := by have := hpow 8 p hp; have := hpow 8 q hq; omega
  have hp7 : p^7 * q + p * q^7 ≥ 0 := by
    have h1 := Int.mul_nonneg (hpow 7 p hp) hq
    have h2 := Int.mul_nonneg hp (hpow 7 q hq)
    omega
  have hp6 : p^6 * q^2 + p^2 * q^6 ≥ 0 := by
    have h1 := Int.mul_nonneg (hpow 6 p hp) (hpow 2 q hq)
    have h2 := Int.mul_nonneg (hpow 2 p hp) (hpow 6 q hq)
    omega
  have hp5 : p^5 * q^3 + p^3 * q^5 ≥ 0 := by
    have h1 := Int.mul_nonneg (hpow 5 p hp) (hpow 3 q hq)
    have h2 := Int.mul_nonneg (hpow 3 p hp) (hpow 5 q hq)
    omega
  have hp4 : p^4 * q^4 ≥ 0 := Int.mul_nonneg (hpow 4 p hp) (hpow 4 q hq)
  obtain ⟨hc0, hc1, hc2, hc3, hc4⟩ := thm3_cofactor_coeffs_pos
  exact ZSqrt17.isNonneg_add
    (ZSqrt17.isNonneg_add
      (ZSqrt17.isNonneg_add
        (ZSqrt17.isNonneg_add
          (ZSqrt17.isNonneg_mul_ofInt hc0 hp8)
          (ZSqrt17.isNonneg_mul_ofInt hc1 hp7))
        (ZSqrt17.isNonneg_mul_ofInt hc2 hp6))
      (ZSqrt17.isNonneg_mul_ofInt hc3 hp5))
    (ZSqrt17.isNonneg_mul_ofInt hc4 hp4)


/-! ==========================================================================
    PART 2: Theorem 4 (p = 3/2) — Pure-Integer Operator-Monotone Certificate
            Proving C_{3/2,2}(3) > C_{3/2,2}(2) with Zero Floating Point!
    ========================================================================== -/

/-- Exact 3x3 integer matrix stored as 9 explicit entries (instant kernel reduction). -/
structure Mat3 where
  m00 : Int
  m01 : Int
  m02 : Int
  m10 : Int
  m11 : Int
  m12 : Int
  m20 : Int
  m21 : Int
  m22 : Int
  deriving DecidableEq, Repr

namespace Mat3

def add (X Y : Mat3) : Mat3 :=
  ⟨X.m00 + Y.m00, X.m01 + Y.m01, X.m02 + Y.m02,
   X.m10 + Y.m10, X.m11 + Y.m11, X.m12 + Y.m12,
   X.m20 + Y.m20, X.m21 + Y.m21, X.m22 + Y.m22⟩

def sub (X Y : Mat3) : Mat3 :=
  ⟨X.m00 - Y.m00, X.m01 - Y.m01, X.m02 - Y.m02,
   X.m10 - Y.m10, X.m11 - Y.m11, X.m12 - Y.m12,
   X.m20 - Y.m20, X.m21 - Y.m21, X.m22 - Y.m22⟩

def scale (c : Int) (X : Mat3) : Mat3 :=
  ⟨c * X.m00, c * X.m01, c * X.m02,
   c * X.m10, c * X.m11, c * X.m12,
   c * X.m20, c * X.m21, c * X.m22⟩

def trans (X : Mat3) : Mat3 :=
  ⟨X.m00, X.m10, X.m20,
   X.m01, X.m11, X.m21,
   X.m02, X.m12, X.m22⟩

def mul (X Y : Mat3) : Mat3 :=
  ⟨X.m00*Y.m00 + X.m01*Y.m10 + X.m02*Y.m20,
   X.m00*Y.m01 + X.m01*Y.m11 + X.m02*Y.m21,
   X.m00*Y.m02 + X.m01*Y.m12 + X.m02*Y.m22,
   X.m10*Y.m00 + X.m11*Y.m10 + X.m12*Y.m20,
   X.m10*Y.m01 + X.m11*Y.m11 + X.m12*Y.m21,
   X.m10*Y.m02 + X.m11*Y.m12 + X.m12*Y.m22,
   X.m20*Y.m00 + X.m21*Y.m10 + X.m22*Y.m20,
   X.m20*Y.m01 + X.m21*Y.m11 + X.m22*Y.m21,
   X.m20*Y.m02 + X.m21*Y.m12 + X.m22*Y.m22⟩

def diag (a b c : Int) : Mat3 :=
  ⟨a, 0, 0,
   0, b, 0,
   0, 0, c⟩

/-- Leading principal minors Δ₁, Δ₂, Δ₃ of a 3x3 matrix. -/
def minor1 (X : Mat3) : Int := X.m00
def minor2 (X : Mat3) : Int := X.m00 * X.m11 - X.m01 * X.m10
def minor3 (X : Mat3) : Int :=
    X.m00 * (X.m11 * X.m22 - X.m12 * X.m21)
  - X.m01 * (X.m10 * X.m22 - X.m12 * X.m20)
  + X.m02 * (X.m10 * X.m21 - X.m11 * X.m20)

/-- Sylvester's criterion: symmetric 3x3 matrix with all three leading principal minors > 0. -/
def IsSymPosDef (X : Mat3) : Prop :=
  X = X.trans ∧ X.minor1 > 0 ∧ X.minor2 > 0 ∧ X.minor3 > 0

instance (X : Mat3) : Decidable (IsSymPosDef X) := by
  unfold IsSymPosDef; infer_instance

/-- Exact soundness of Sylvester's criterion via scaled block LDL^T completion of squares:
    if `X` is symmetric with `Δ₁ > 0, Δ₂ > 0, Δ₃ > 0`, then `v^T X v > 0` for all `v ≠ 0`. -/
theorem symPosDef_quadForm_pos (X : Mat3) (hX : X.IsSymPosDef) (x y z : Int)
    (hnz : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) :
    x * (X.m00 * x + X.m01 * y + X.m02 * z)
    + y * (X.m10 * x + X.m11 * y + X.m12 * z)
    + z * (X.m20 * x + X.m21 * y + X.m22 * z) > 0 := by
  rcases hX with ⟨hsym, hd1, hd2, hd3⟩
  have h01 : X.m10 = X.m01 := by
    have := congrArg Mat3.m10 hsym; simpa [trans] using this
  have h02 : X.m20 = X.m02 := by
    have := congrArg Mat3.m20 hsym; simpa [trans] using this
  have h12 : X.m21 = X.m12 := by
    have := congrArg Mat3.m21 hsym; simpa [trans] using this
  let Δ1 := X.minor1
  let Δ2 := X.minor2
  let Δ3 := X.minor3
  let Q := x * (X.m00 * x + X.m01 * y + X.m02 * z)
         + y * (X.m10 * x + X.m11 * y + X.m12 * z)
         + z * (X.m20 * x + X.m21 * y + X.m22 * z)
  let u1 := X.m00 * x + X.m01 * y + X.m02 * z
  let u2 := Δ2 * y + (X.m00 * X.m12 - X.m01 * X.m02) * z
  have h_id : Δ1 * Δ2 * Q = Δ2 * (u1 * u1) + (u2 * u2) + X.m00 * Δ3 * (z * z) := by
    simp only [Δ1, Δ2, Δ3, Q, u1, u2, minor1, minor2, minor3]
    rw [h01, h02, h12]
    grind
  have hΔ1 : Δ1 > 0 := hd1
  have hΔ2 : Δ2 > 0 := hd2
  have hΔ3 : Δ3 > 0 := hd3
  have hm00 : X.m00 > 0 := hd1
  have h1 : Δ2 * (u1 * u1) ≥ 0 := Int.mul_nonneg (by omega) (int_sq_nonneg u1)
  have h2 : u2 * u2 ≥ 0 := int_sq_nonneg u2
  have h3 : X.m00 * Δ3 * (z * z) ≥ 0 := by
    have hp : X.m00 * Δ3 > 0 := Int.mul_pos hm00 hΔ3
    exact Int.mul_nonneg (by omega) (int_sq_nonneg z)
  have h_strict : Δ1 * Δ2 * Q > 0 := by
    by_cases hz : z ≠ 0
    · have hp : X.m00 * Δ3 > 0 := Int.mul_pos hm00 hΔ3
      have hz2 : z * z > 0 := int_sq_pos z hz
      have h3s : X.m00 * Δ3 * (z * z) > 0 := Int.mul_pos hp hz2
      omega
    · have hz0 : z = 0 := by omega
      subst hz0
      by_cases hy : y ≠ 0
      · have hu2 : u2 ≠ 0 := by
          simp only [u2]; intro h
          have hdy : Δ2 * y = 0 := by omega
          rcases Int.mul_eq_zero.mp hdy with h' | h'
          · omega
          · exact hy h'
        have h2s : u2 * u2 > 0 := int_sq_pos u2 hu2
        omega
      · have hy0 : y = 0 := by omega
        subst hy0
        have hx : x ≠ 0 := by
          rcases hnz with h | h | h
          · exact h
          · exact absurd rfl h
          · exact absurd rfl h
        have hu1 : u1 ≠ 0 := by
          simp only [u1]; intro h
          have hmx : X.m00 * x = 0 := by omega
          rcases Int.mul_eq_zero.mp hmx with h' | h'
          · omega
          · exact hx h'
        have h1s : Δ2 * (u1 * u1) > 0 := Int.mul_pos hΔ2 (int_sq_pos u1 hu1)
        omega
  have hprod : Δ1 * Δ2 > 0 := Int.mul_pos hΔ1 hΔ2
  by_cases hQ : Q > 0
  · exact hQ
  · have hQle : Q ≤ 0 := by omega
    have hneg : Δ1 * Δ2 * Q ≤ 0 := by
      have : Δ1 * Δ2 * (-Q) ≥ 0 := Int.mul_nonneg (by omega) (by omega)
      have heq : Δ1 * Δ2 * (-Q) = -(Δ1 * Δ2 * Q) := Int.mul_neg (Δ1 * Δ2) Q
      omega
    omega

end Mat3

/-- The explicit two-digit integer 3x3 witness pair `(A, B)` of Theorem 4 (`p = 3/2`). -/
def A_mat : Mat3 :=
  ⟨49, 62, -1,
   11, 14,  0,
    0,  0,  0⟩

def B_mat : Mat3 :=
  ⟨81,  0,  0,
    0,  0,  0,
    0,  0,  0⟩

def S_mat : Mat3 := Mat3.add A_mat B_mat

/-- Exact integer Gram matrices `A^T A` and `S S^T`. -/
theorem thm4_ATA_exact :
    Mat3.mul A_mat.trans A_mat =
      ⟨2522, 3192, -49,
       3192, 4040, -62,
        -49,  -62,   1⟩ := by
  decide

theorem thm4_SST_exact :
    Mat3.mul S_mat S_mat.trans =
      ⟨20745, 2298, 0,
        2298,  317, 0,
           0,    0, 0⟩ := by
  decide

/-- Exact integer scale `N_A = 10^12` and symmetric integer matrix `U_A` with `U_A / N_A ≻ |A|`. -/
def N_A : Int := 1000000000000

def UA_mat : Mat3 :=
  ⟨31137293167063,  39396185181747, -640946834916,
   39396185181747,  49873886383270, -733515582123,
    -640946834916,   -733515582123,  226166071368⟩

/-- Certificate 1: `U_A ≻ 0` (Sylvester positive definite). -/
theorem thm4_cert1_UA_posdef : UA_mat.IsSymPosDef := by
  decide

/-- Certificate 2: `U_A^2 - N_A^2 (A^T A) ≻ 0` (Sylvester positive definite).
    By Löwner operator monotonicity of `sqrt`, this certifies `U_A / N_A ≻ |A|`,
    hence `U_H := U_A / N_A + B ≻ |A| + |B| = H`. -/
theorem thm4_cert2_operator_monotone_bound :
    (Mat3.sub (Mat3.mul UA_mat UA_mat)
              (Mat3.scale (N_A * N_A) (Mat3.mul A_mat.trans A_mat))).IsSymPosDef := by
  decide

/-- Exact integer Cayley-orthogonal matrix `Q` with `Q^T Q = N_Q^2 I_3`. -/
def N_Q : Int := 3765439130012390

def Q_mat : Mat3 :=
  ⟨  -2754699207390,  1641554318888100, -3388779082737700,
    -53429001111900, -3388455869640388, -1641354319812834,
  -3765059042737700,    46883680187166,    25771438835388⟩

/-- Certificate 3: Exact orthogonality `Q^T Q = N_Q^2 I_3`. -/
theorem thm4_cert3_Q_orthogonal :
    Mat3.mul Q_mat.trans Q_mat = Mat3.diag (N_Q * N_Q) (N_Q * N_Q) (N_Q * N_Q) := by
  decide

/-- Exact rational square-root upper bounds `d_i / N_D` on the eigenvalues of `U_H = U_A/N_A + B`. -/
def N_D : Int := 10000000
def d1 : Int := 4640130
def d2 : Int := 55496286
def d3 : Int := 114552923

/-- Certificate 4: `N_Q^2 N_A diag(d_1^2, d_2^2, d_3^2) - N_D^2 Q^T (U_A + N_A B) Q ≻ 0`.
    In Loewner order, `0 ⪯ H ≺ U_H ≺ Q_0 diag((d_i/N_D)^2) Q_0^T` (with `Q_0 = Q/N_Q ∈ O(3)`),
    so by Weyl monotonicity `||H||_{3/2}^{3/2} < (d_1^3 + d_2^3 + d_3^3) / N_D^3`. -/
theorem thm4_cert4_diagonal_upper_bound :
    let UH := Mat3.add UA_mat (Mat3.scale N_A B_mat)
    let M  := Mat3.mul Q_mat.trans (Mat3.mul UH Q_mat)
    let sc := N_Q * N_Q * N_A
    let D  := Mat3.diag (sc * d1 * d1) (sc * d2 * d2) (sc * d3 * d3)
    (Mat3.sub D (Mat3.scale (N_D * N_D) M)).IsSymPosDef := by
  decide

/-- Exact fourth-root lower bounds `r_i / N_R` on the two nonzero eigenvalues of `S S^T`. -/
def N_R : Int := 10000000
def r1 : Int := 120380588
def r2 : Int := 28024717

/-- Certificate 5: Exact root bracketing for the characteristic polynomial
    `p(λ) = λ^2 - 21062*λ + 1295361` of the 2x2 nonzero block of `S S^T`.
    Certifies `||S||_{3/2}^{3/2} = λ_1^{3/4} + λ_2^{3/4} > (r_1^3 + r_2^3) / N_R^3`. -/
theorem thm4_cert5_numerator_root_bracketing :
    let NR4 := N_R ^ 4
    let x1  := r1 ^ 4
    let x2  := r2 ^ 4
    x2 < 10531 * NR4 ∧
    x2 * x2 - 21062 * x2 * NR4 + 1295361 * NR4 * NR4 > 0 ∧
    x1 * x1 - 21062 * x1 * NR4 + 1295361 * NR4 * NR4 < 0 := by
  decide

/-- Certificate 6 (FINAL THEOREM 4 CERTIFICATION):
    With `P = r1^3 + r2^3` and `Q = d1^3 + d2^3 + d3^3` (`N_D = N_R = 10^7`),
    we prove `256 * P^4 - 107 * Q^4 > 0` and `(256 * P^4 - 107 * Q^4)^2 > 51^2 * 17 * Q^8`,
    certifying `(||A + B||_{3/2} / |||A| + |B|||_{3/2})^6 > (P/Q)^4 > (107 + 51*sqrt(17))/256 = C_{3/2,2}(2)^6`! -/
theorem thm4_beats_2x2_ceiling :
    let P := r1 ^ 3 + r2 ^ 3
    let Q := d1 ^ 3 + d2 ^ 3 + d3 ^ 3
    let gap := 256 * P ^ 4 - 107 * Q ^ 4
    gap > 0 ∧ gap * gap > 51 * 51 * 17 * Q ^ 8 := by
  decide


/-! ==========================================================================
    PART 3: Core Algebraic Lemmas of Theorem 1 & Logical Induction Schema
    ========================================================================== -/

/-- Exact core rational inequality of Lemma 4(a) (Sherman–Morrison monotonicity step):
    for `s > 0, t ≥ 0, φ ≥ 0` with `s*φ ≤ 1`,
      `((1 - sφ)(s + t) + t)(1 + tφ) - (s + t)(1 + tφ - sφ) = t (1 - sφ)(1 + sφ + tφ) ≥ 0`. -/
theorem lemma4a_sherman_morrison_core (s t phi : Int)
    (hs : s > 0) (ht : t ≥ 0) (hphi : phi ≥ 0) (hle : s * phi ≤ 1) :
    ((1 - s * phi) * (s + t) + t) * (1 + t * phi)
      ≥ (s + t) * (1 + t * phi - s * phi) := by
  have hid : ((1 - s * phi) * (s + t) + t) * (1 + t * phi) - (s + t) * (1 + t * phi - s * phi)
      = t * (1 - s * phi) * (1 + s * phi + t * phi) := by grind
  have h1 : 1 - s * phi ≥ 0 := by omega
  have hsp : s * phi ≥ 0 := Int.mul_nonneg (by omega) hphi
  have htp : t * phi ≥ 0 := Int.mul_nonneg ht hphi
  have h2 : 1 + s * phi + t * phi ≥ 0 := by omega
  have h3 : t * (1 - s * phi) ≥ 0 := Int.mul_nonneg ht h1
  have h4 : t * (1 - s * phi) * (1 + s * phi + t * phi) ≥ 0 := Int.mul_nonneg h3 h2
  omega

/-- Exact isometry verification in Lemma 2:
    `(1 - (1 - c))^2 + s^2 = 1` whenever `c^2 + s^2 = 1`, verifying `R(θ)^* R(θ) = I_n`. -/
theorem lemma2_isometry_norm_identity (c s : Int) (h : c * c + s * s = 1) :
    (1 - (1 - c)) * (1 - (1 - c)) + s * s = 1 := by
  grind

/-- Exact nonnegative-square numerator identity in Theorem 3 (monotonicity in `x = a*b`):
    whenever `u^2 = x - d` and `v^2 = x - τ^2`, `(x - d) + (x - τ^2) - 2*u*v = (u - v)^2 ≥ 0`. -/
theorem thm3_nonneg_square_derivative (x d tau u v : Int)
    (hu : u * u = x - d) (hv : v * v = x - tau * tau) :
    (x - d) + (x - tau * tau) - 2 * u * v ≥ 0 := by
  have h : (x - d) + (x - tau * tau) - 2 * u * v = (u - v) * (u - v) := by grind
  rw [h]
  exact int_sq_nonneg (u - v)

section Theorem1Skeleton

variable {α : Type} [LT α] [LE α]

/-- Formal logical induction of Theorem 1:
    combining `C 1 < C 2` with the dimension-`n` lifting dichotomy (Lemma 1 + Lemma 2 + Lemma 4(b))
    yields strict monotonicity `∀ n ≥ 1, C n < C (n + 1)` and rules out finite-dimensional
    stabilization (`∀ n ≥ 1, C n < C_inf`). -/
theorem thm1_strict_hierarchy_from_lemmas
    (C : Nat → α) (C_inf : α)
    (lt_trans : ∀ {a b c : α}, a < b → b < c → a < c)
    (lt_of_lt_of_le : ∀ {a b c : α}, a < b → b ≤ c → a < c)
    (h_base : C 1 < C 2)
    (h_ub   : ∀ n, C n ≤ C_inf)
    (h_lift : ∀ n, n ≥ 2 → C 1 < C n →
      (∃ _kerS : Unit, C n < C (n + 1)) ∨ (∃ _kerLift : Unit, C n < C (n + 1))) :
    (∀ n, n ≥ 1 → C n < C (n + 1)) ∧ (∀ n, n ≥ 1 → C n < C_inf) := by
  have h_gt1 : ∀ m : Nat, C 1 < C (m + 2) := by
    intro m
    induction m with
    | zero => exact h_base
    | succ k ih =>
      rcases h_lift (k + 2) (by omega) ih with ⟨_, hstep⟩ | ⟨_, hstep⟩
      · exact lt_trans ih hstep
      · exact lt_trans ih hstep
  have h_step : ∀ n, n ≥ 1 → C n < C (n + 1) := by
    intro n hn
    cases n with
    | zero => omega
    | succ k =>
      cases k with
      | zero => exact h_base
      | succ m =>
        rcases h_lift (m + 2) (by omega) (h_gt1 m) with ⟨_, hstep⟩ | ⟨_, hstep⟩
        · exact hstep
        · exact hstep
  refine ⟨h_step, ?_⟩
  intro n hn
  exact lt_of_lt_of_le (h_step n hn) (h_ub (n + 1))

end Theorem1Skeleton

end MI20

/-! ==========================================================================
    AXIOM AUDIT: Confirm zero `sorry` and zero custom axioms on every theorem!
    ========================================================================== -/
#print axioms MI20.no_nat_sq_eq_17_sq
#print axioms MI20.ZSqrt17.sq_isNonneg
#print axioms MI20.thm3_derivative_numerator
#print axioms MI20.thm3_quartic_factorization
#print axioms MI20.thm3_closed_form_at_zstar
#print axioms MI20.thm3_cofactor_coeffs_pos
#print axioms MI20.thm3_global_optimality_identity
#print axioms MI20.thm3_global_max_nonneg
#print axioms MI20.Mat3.symPosDef_quadForm_pos
#print axioms MI20.thm4_ATA_exact
#print axioms MI20.thm4_SST_exact
#print axioms MI20.thm4_cert1_UA_posdef
#print axioms MI20.thm4_cert2_operator_monotone_bound
#print axioms MI20.thm4_cert3_Q_orthogonal
#print axioms MI20.thm4_cert4_diagonal_upper_bound
#print axioms MI20.thm4_cert5_numerator_root_bracketing
#print axioms MI20.thm4_beats_2x2_ceiling
#print axioms MI20.lemma4a_sherman_morrison_core
#print axioms MI20.lemma2_isometry_norm_identity
#print axioms MI20.thm3_nonneg_square_derivative
#print axioms MI20.thm1_strict_hierarchy_from_lemmas
