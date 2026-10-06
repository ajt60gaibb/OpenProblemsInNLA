/-
The finite first-failure induction for selected-block spectral profiles.
Exact contracts were independently reviewed before implementation in
reviews/spectral-recursion-specification.md. The reusable conditional theorem
below must be instantiated with the actual proved selected-block extension;
no manuscript estimate is asserted as an axiom.
-/
import NLA.IE06.GaussianSpectralBase
import NLA.IE06.ProfileSum

set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal
namespace NLA.IE06.GaussianSpectralRecursion
open GaussianSpectralBase Spectral ScalarRecurrence SpectralRecursionScalars

theorem block_singularValue_congr {n t u : ℕ} (h : t=u) (ht : t≤n) (hu : u≤n)
    (A : Mat n) (j : ℕ) : singularValue (block ht A) j=singularValue (block hu A) j := by
  subst u
  rfl

def stageGood {n : ℕ} (r₀ : ℕ) (g : ℕ → ℝ) (A : Mat n) (t : ℕ) (ht : t≤n) : Prop :=
  ∀ d, r₀≤d → d<t → g d ≤ singularValue (block ht A) (t-d-1)

def globalBad (n r₀ : ℕ) (g : ℕ → ℝ) : Set (Mat n) :=
  {A | ∃ t, ∃ ht : t≤n, ∃ d, r₀≤d ∧ d<t ∧ singularValue (block ht A) (t-d-1)<g d}

/-- The pair index has exactly n squared possibilities: t is one plus the
first Fin n coordinate, and d is the second. -/
def localBad {n : ℕ} (r₀ : ℕ) (g : ℕ → ℝ) (ℓ : ℝ) (p : Fin n × Fin n) : Set (Mat n) :=
  let t := p.1.val+1
  let d := p.2.val
  let ht : t≤n := Nat.succ_le_of_lt p.1.isLt
  {A | r₀≤d ∧ d<t ∧ singularValue (block ht A) (t-d-1)<g d ∧
    (8*step ℓ d<t → stageGood r₀ g A (t-4*step ℓ d) ((Nat.sub_le _ _).trans ht))}

theorem globalBad_subset_localBad {n r₀ : ℕ} (hr : 0<r₀) (g : ℕ → ℝ) (ℓ : ℝ) :
    globalBad n r₀ g ⊆ ⋃ p : Fin n × Fin n, localBad r₀ g ℓ p := by
  intro A hA
  by_contra hnone
  have hgood : ∀ t, ∀ ht : t≤n, stageGood r₀ g A t ht := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro ht d hdr hdt
      by_contra hfail
      have hlt : singularValue (block ht A) (t-d-1)<g d := lt_of_not_ge hfail
      have hd : 0<d := hr.trans_le hdr
      have ht0 : 0<t := hd.trans hdt
      let i : Fin n := ⟨t-1,by omega⟩
      let j : Fin n := ⟨d,lt_of_lt_of_le hdt ht⟩
      have hte : t-1+1=t := by omega
      have hval := block_singularValue_congr hte (Nat.succ_le_of_lt i.isLt) ht A (t-d-1)
      have hp : A∈localBad r₀ g ℓ (i,j) := by
        simp only [localBad,i,j,hte]
        refine ⟨hdr,hdt,?_,?_⟩
        · exact hval.trans_lt hlt
        · intro hstep
          have hk : 0<step ℓ d := step_pos ℓ hd
          exact ih (t-4*step ℓ d) (by omega) ((Nat.sub_le _ _).trans ht)
      exact hnone (Set.mem_iUnion.mpr ⟨(i,j),hp⟩)
  obtain ⟨t,ht,d,hdr,hdt,hbad⟩ := hA
  exact not_lt_of_ge (hgood t ht d hdr hdt) hbad

/-- Exact source B4 as an ordinary reusable theorem interface. This definition
is not a claim that the bound holds; the final Gaussian theorem must supply
the independently proved unconditional selected-block extension theorem. -/
def ExtensionBound (n : ℕ) (β C : ℝ) : Prop :=
  ∀ (m k d : ℕ) (ht : m+4*k ≤ n), k < m → 16 ≤ d → 100*d ≤ k → ∀ μ : ℝ,
    0 < μ → μ < Real.sqrt k →
    gaussianMatrix n {A |
      μ ≤ singularValue (block ((Nat.le_add_right m (4*k)).trans ht) A) (m-k-1) ∧
      TruncatedInverse.sigmaInvSum (block ((Nat.le_add_right m (4*k)).trans ht) A) k≤2*k*(μ⁻¹)^2 ∧
      singularValue (block ht A) (m+4*k-d-1)≤
        (μ*d/k)*Real.exp (-C*(1+(k:ℝ)*Real.log (n:ℝ)/(d:ℝ)^2))}
      ≤ENNReal.ofReal (Real.exp (-β*Real.log (n:ℝ)))

theorem localBad_tail_of_extension_bound {n : ℕ}
    (hlog : 256≤Real.log (n:ℝ)) {β C D : ℝ} (hβ : 1≤β) (hC : 0≤C)
    (hDbase : 4*β+4004≤D) (hDrec : 100*C≤D) (hB : ExtensionBound n β C)
    (p : Fin n × Fin n) :
    gaussianMatrix n (localBad ⌈Real.sqrt (Real.log (n:ℝ))⌉₊
      (profile n (Real.log (n:ℝ)) D) (Real.log (n:ℝ)) p) ≤
      ENNReal.ofReal (Real.exp (-β*Real.log (n:ℝ))) := by
  let t := p.1.val+1
  let d := p.2.val
  let ℓ := Real.log (n:ℝ)
  let r₀ := ⌈Real.sqrt ℓ⌉₊
  let g := profile n ℓ D
  have ht : t≤n := Nat.succ_le_of_lt p.1.isLt
  have hℓ : 0<ℓ := by dsimp only [ℓ]; linarith
  have hDn : 0≤D := by linarith
  change gaussianMatrix n (localBad r₀ g ℓ p)≤_
  by_cases hdr : r₀≤d
  swap
  · have he : localBad r₀ g ℓ p=∅ := Set.eq_empty_iff_forall_notMem.mpr (fun _ h => hdr h.1)
    rw [he,measure_empty]
    exact bot_le
  by_cases hdt : d<t
  swap
  · have he : localBad r₀ g ℓ p=∅ := Set.eq_empty_iff_forall_notMem.mpr (fun _ h => hdt h.2.1)
    rw [he,measure_empty]
    exact bot_le
  by_cases hbase : t≤8*step ℓ d
  · apply (measure_mono (show localBad r₀ g ℓ p ⊆
        {A | singularValue (block ht A) (t-d-1)<g d} from fun _ h => h.2.2.1)).trans
    exact selected_block_profile_base ht hdt hlog hdr hβ hDbase hbase
  let k := step ℓ d
  let u := t-4*k
  have hsmall : 8*k<t := Nat.lt_of_not_ge hbase
  have hd16 : 16≤d := (sixteen_le_ceil_sqrt hlog).trans hdr
  have hd : 0<d := by omega
  have hdk : d≤k := step_ge_self ℓ d
  have hk : 0<k := step_pos ℓ hd
  have hku : k<u := by dsimp only [u]; omega
  have huk : u+4*k=t := by dsimp only [u]; omega
  have hut : u<t := by dsimp only [u]; omega
  have hkn : k<n := by omega
  have hn : 0<n := by omega
  have hμ : 0<g k := profile_pos hn hk ℓ D
  have hμk : g k<Real.sqrt k := profile_lt_sqrt hk hkn hℓ.le hDn
  have hdim : u+4*k≤n := by omega
  have hbu := hB u k d hdim hku hd16 (step_ge_linear ℓ d) (g k) hμ hμk
  apply (measure_mono ?_).trans hbu
  intro A hA
  have hprev : stageGood r₀ g A u ((Nat.sub_le _ _).trans ht) := hA.2.2.2 hsmall
  refine ⟨hprev k (hdr.trans hdk) hku,?_,?_⟩
  · have hs := ProfileSum.sigmaInvSum_le_scalarProfile
      (block ((Nat.sub_le _ _).trans ht) A) hn hk hℓ hDn
      (fun q hkq hqu => hprev q ((hdr.trans hdk).trans hkq) hqu)
    simpa only [g,div_eq_mul_inv,inv_pow] using hs
  · have hrec := profile_recurrence_le hn hd (hdt.trans_le ht) hℓ hC hDrec
    have hfail : singularValue (block ht A) (t-d-1)<g d := hA.2.2.1
    have hout := hfail.le.trans hrec
    rw [show u+4*k-d-1=t-d-1 by rw [huk]]
    exact (block_singularValue_congr huk hdim ht A (t-d-1)).trans_le hout

theorem dimension_union_exponential (n : ℕ) (hn : 0<n) (β : ℝ) :
    (n:ℝ≥0∞)^2*ENNReal.ofReal (Real.exp (-β*Real.log (n:ℝ)))=
      ENNReal.ofReal (Real.exp (-(β-2)*Real.log (n:ℝ))) := by
  rw [← ENNReal.ofReal_natCast n,← ENNReal.ofReal_pow (Nat.cast_nonneg n),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hn2 : (n:ℝ)^2=Real.exp (2*Real.log (n:ℝ)) := by
    rw [show 2*Real.log (n:ℝ)=Real.log (n:ℝ)+Real.log (n:ℝ) by ring,
      Real.exp_add,Real.exp_log hnR,pow_two]
  rw [hn2,← Real.exp_add]
  congr 1
  ring

/-- Every local failure is paid once. This is a reusable theorem conditional
on B4; the final unconditional exported result must supply that proved bound. -/
theorem profile_tail_of_extension_bound {n : ℕ} (hlog : 256≤Real.log (n:ℝ))
    {β C D : ℝ} (hβ : 1≤β) (hC : 0≤C) (hDbase : 4*β+4004≤D)
    (hDrec : 100*C≤D) (hB : ExtensionBound n β C) :
    gaussianMatrix n (globalBad n ⌈Real.sqrt (Real.log (n:ℝ))⌉₊
      (profile n (Real.log (n:ℝ)) D)) ≤
      ENNReal.ofReal (Real.exp (-(β-2)*Real.log (n:ℝ))) := by
  have hr : 0<⌈Real.sqrt (Real.log (n:ℝ))⌉₊ := lt_of_lt_of_le (by norm_num) (sixteen_le_ceil_sqrt hlog)
  have hn : 0<n := by
    by_contra h
    have hn0 : n=0 := Nat.eq_zero_of_not_pos h
    norm_num [hn0] at hlog
  calc
    _ ≤ gaussianMatrix n (⋃ p : Fin n × Fin n,
        localBad ⌈Real.sqrt (Real.log (n:ℝ))⌉₊ (profile n (Real.log (n:ℝ)) D) (Real.log (n:ℝ)) p) :=
      measure_mono (globalBad_subset_localBad hr _ _)
    _ ≤ (Fintype.card (Fin n × Fin n):ℝ≥0∞)*ENNReal.ofReal (Real.exp (-β*Real.log (n:ℝ))) :=
      measure_finite_iUnion_le _ _ _ (localBad_tail_of_extension_bound hlog hβ hC hDbase hDrec hB)
    _ = _ := by
      simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
      rw [← pow_two,dimension_union_exponential n hn β]

theorem profile_inverse_identity {n r : ℕ} (hn : 0<n) (hr : 0<r) (ℓ D : ℝ) :
    2*r/(profile n ℓ D r)^2=(2*n/(r:ℝ))*Real.exp (2*D*cost n ℓ r) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hrR : (0:ℝ)<r := by exact_mod_cast hr
  have he : Real.exp (-D*cost n ℓ r)^2=(Real.exp (2*D*cost n ℓ r))⁻¹ := by
    rw [pow_two,← Real.exp_add,← Real.exp_neg]
    congr 1
    ring
  unfold profile
  rw [mul_pow,div_pow,Real.sq_sqrt hnR.le,he]
  field_simp

theorem profile_inverse_bound {n r : ℕ} (hlog : 256≤Real.log (n:ℝ))
    (hr : ⌈Real.sqrt (Real.log (n:ℝ))⌉₊≤r) {D : ℝ} (hD : 0≤D) :
    2*r/(profile n (Real.log (n:ℝ)) D r)^2 ≤
      (2*n/(r:ℝ))*Real.exp (12*D*Real.sqrt (Real.log (n:ℝ))) := by
  have hn : 0<n := by
    by_contra h
    have hn0 : n=0 := Nat.eq_zero_of_not_pos h
    norm_num [hn0] at hlog
  have hr0 : 0<r := lt_of_lt_of_le (by norm_num) ((sixteen_le_ceil_sqrt hlog).trans hr)
  rw [profile_inverse_identity hn hr0]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hc := mul_le_mul_of_nonneg_left (cost_le_six_sqrt hn hlog hr)
    (mul_nonneg (by norm_num : (0:ℝ)≤2) hD)
  nlinarith only [hc]

def inverseBad (n r₀ : ℕ) (D : ℝ) : Set (Mat n) :=
  {A | ∃ t, ∃ ht : t≤n, ∃ r, r₀≤r ∧
    (2*n/(r:ℝ))*Real.exp (12*D*Real.sqrt (Real.log (n:ℝ)))<
      TruncatedInverse.sigmaInvSum (block ht A) r}

theorem inverseBad_subset_globalBad {n : ℕ} (hlog : 256≤Real.log (n:ℝ))
    {D : ℝ} (hD : 0≤D) :
    inverseBad n ⌈Real.sqrt (Real.log (n:ℝ))⌉₊ D ⊆
      globalBad n ⌈Real.sqrt (Real.log (n:ℝ))⌉₊ (profile n (Real.log (n:ℝ)) D) := by
  intro A hA
  by_contra hnot
  obtain ⟨t,ht,r,hr,hbad⟩ := hA
  have hr0 : 0<r := lt_of_lt_of_le (by norm_num) ((sixteen_le_ceil_sqrt hlog).trans hr)
  have hn : 0<n := by
    by_contra h
    have hn0 : n=0 := Nat.eq_zero_of_not_pos h
    norm_num [hn0] at hlog
  have hℓ : 0<Real.log (n:ℝ) := by linarith
  have hg : ∀ d, r≤d → d<t → profile n (Real.log (n:ℝ)) D d≤
      singularValue (block ht A) (t-d-1) := by
    intro d hrd hdt
    by_contra hfail
    exact hnot ⟨t,ht,d,hr.trans hrd,hdt,lt_of_not_ge hfail⟩
  have hs := ProfileSum.sigmaInvSum_le_scalarProfile (block ht A) hn hr0 hℓ hD hg
  exact not_lt_of_ge (hs.trans (profile_inverse_bound hlog hr hD)) hbad

/-- The sufficient simultaneous retained-inverse bound for the unchanged
IE-06 final target, still exposing B4 until its actual theorem is supplied. -/
theorem inverse_tail_of_extension_bound {n : ℕ} (hlog : 256≤Real.log (n:ℝ))
    {β C D : ℝ} (hβ : 1≤β) (hC : 0≤C) (hDbase : 4*β+4004≤D)
    (hDrec : 100*C≤D) (hB : ExtensionBound n β C) :
    gaussianMatrix n (inverseBad n ⌈Real.sqrt (Real.log (n:ℝ))⌉₊ D)≤
      ENNReal.ofReal (Real.exp (-(β-2)*Real.log (n:ℝ))) := by
  exact (measure_mono (inverseBad_subset_globalBad hlog (by linarith))).trans
    (profile_tail_of_extension_bound hlog hβ hC hDbase hDrec hB)

#assert_trust kernel block_singularValue_congr
#print axioms block_singularValue_congr
#assert_trust kernel stageGood
#print axioms stageGood
#assert_trust kernel globalBad
#print axioms globalBad
#assert_trust kernel localBad
#print axioms localBad
#assert_trust kernel globalBad_subset_localBad
#print axioms globalBad_subset_localBad
#assert_trust kernel ExtensionBound
#print axioms ExtensionBound
#assert_trust kernel localBad_tail_of_extension_bound
#print axioms localBad_tail_of_extension_bound
#assert_trust kernel dimension_union_exponential
#print axioms dimension_union_exponential
#assert_trust kernel profile_tail_of_extension_bound
#print axioms profile_tail_of_extension_bound
#assert_trust kernel profile_inverse_identity
#print axioms profile_inverse_identity
#assert_trust kernel profile_inverse_bound
#print axioms profile_inverse_bound
#assert_trust kernel inverseBad
#print axioms inverseBad
#assert_trust kernel inverseBad_subset_globalBad
#print axioms inverseBad_subset_globalBad
#assert_trust kernel inverse_tail_of_extension_bound
#print axioms inverse_tail_of_extension_bound
end NLA.IE06.GaussianSpectralRecursion
