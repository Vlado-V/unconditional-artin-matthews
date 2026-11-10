module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.NumberTheory.AbelSummation


set_option backward.privateInPublic true
@[expose] public section

/-! Weighted sharp-interval discrepancy for genuine Lipschitz test functions.
The discrete and continuous measures are compared using absolute continuity,
with the boundary term retained explicitly. -/
namespace ArtinMatthews
open Finset MeasureTheory Filter
open scoped Topology NNReal
noncomputable section

section RealAbel
variable (c : ℕ → ℝ) {f : ℝ → ℝ} {a b : ℝ}
open intervalIntegral IntervalIntegrable

private theorem weightedDiscrepancy_sumlocc {m : ℕ} (n : ℕ) :
    ∀ᵐ t, t ∈ Set.Icc (n : ℝ) (n + 1) → ∑ k ∈ Icc m ⌊t⌋₊, c k = ∑ k ∈ Icc m n, c k := by
  filter_upwards [Ico_ae_eq_Icc] with t h ht
  rw [Nat.floor_eq_on_Ico _ _ (h.mpr ht)]

open scoped Interval in
private theorem weightedDiscrepancy_integralmulsum (hf : AbsolutelyContinuousOnInterval f a b)
    (_hf_int : IntegrableOn (deriv f) (Set.Icc a b)) (t₁ t₂ : ℝ) (n : ℕ) (h : t₁ ≤ t₂)
    (h₁ : n ≤ t₁) (h₂ : t₂ ≤ n + 1) (h₃ : a ≤ t₁) (h₄ : t₂ ≤ b) :
    ∫ t in t₁..t₂, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k =
      (f t₂ - f t₁) * ∑ k ∈ Icc 0 n, c k := by
  have h_inc₁ : Ι t₁ t₂ ⊆ Set.Icc n (n + 1) :=
    Set.uIoc_of_le h ▸ Set.Ioc_subset_Icc_self.trans <| Set.Icc_subset_Icc h₁ h₂
  have h_inc₂ : Set.uIcc t₁ t₂ ⊆ Set.uIcc a b := by
    rw [Set.uIcc_of_le h, Set.uIcc_of_le (h₃.trans (h.trans h₄))]
    exact Set.Icc_subset_Icc h₃ h₄
  rw [← (hf.mono h_inc₂).integral_deriv_eq_sub,
      ← intervalIntegral.integral_mul_const]
  · refine integral_congr_ae ?_
    filter_upwards [weightedDiscrepancy_sumlocc c n] with t h h'
    rw [h (h_inc₁ h')]

private theorem weightedDiscrepancy_ineqofmemIco {k : ℕ} (hk : k ∈ Set.Ico (⌊a⌋₊ + 1) ⌊b⌋₊) :
    a ≤ k ∧ k + 1 ≤ b := by
  constructor
  · have := (Set.mem_Ico.mp hk).1
    exact le_of_lt <| (Nat.floor_lt' (by lia)).mp this
  · rw [← Nat.cast_add_one, ← Nat.le_floor_iff' (Nat.succ_ne_zero k)]
    exact (Set.mem_Ico.mp hk).2

private theorem weightedDiscrepancy_ineqofmemIco' {k : ℕ} (hk : k ∈ Ico (⌊a⌋₊ + 1) ⌊b⌋₊) :
    a ≤ k ∧ k + 1 ≤ b :=
  weightedDiscrepancy_ineqofmemIco (by rwa [← Finset.coe_Ico])

/-- Abel's summation formula. -/
theorem weightedDiscrepancy_real_abel (ha : 0 ≤ a) (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hf_int : IntegrableOn (deriv f) (Set.Icc a b)) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k * c k =
      f b * (∑ k ∈ Icc 0 ⌊b⌋₊, c k) - f a * (∑ k ∈ Icc 0 ⌊a⌋₊, c k) -
        ∫ t in Set.Ioc a b, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k := by
  rw [← integral_of_le hab]
  have aux1 : ⌊a⌋₊ ≤ a := Nat.floor_le ha
  have aux2 : b ≤ ⌊b⌋₊ + 1 := (Nat.lt_floor_add_one _).le
  obtain hb | hb := eq_or_lt_of_le (Nat.floor_le_floor hab)
  · rw [hb, Ioc_eq_empty_of_le le_rfl, sum_empty, ← sub_mul,
      weightedDiscrepancy_integralmulsum c hf hf_int _ _ ⌊b⌋₊ hab (hb ▸ aux1) aux2 le_rfl le_rfl, sub_self]
  have aux3 : a ≤ ⌊a⌋₊ + 1 := (Nat.lt_floor_add_one _).le
  have aux4 : ⌊a⌋₊ + 1 ≤ b := by rwa [← Nat.cast_add_one, ← Nat.le_floor_iff (ha.trans hab)]
  have aux5 : ⌊b⌋₊ ≤ b := Nat.floor_le (ha.trans hab)
  have aux6 : a ≤ ⌊b⌋₊ := Nat.floor_lt ha |>.mp hb |>.le
  simp_rw [← smul_eq_mul, sum_Ioc_by_parts (fun k ↦ f k) _ hb, range_eq_Ico,
    Ico_add_one_right_eq_Icc, smul_eq_mul]
  have : ∑ k ∈ Ioc ⌊a⌋₊ (⌊b⌋₊ - 1), (f ↑(k + 1) - f k) * ∑ n ∈ Icc 0 k, c n =
        ∑ k ∈ Ico (⌊a⌋₊ + 1) ⌊b⌋₊, ∫ t in k..↑(k + 1), deriv f t * ∑ n ∈ Icc 0 ⌊t⌋₊, c n := by
    rw [← Ico_add_one_add_one_eq_Ioc, Nat.sub_add_cancel (by lia), Eq.comm]
    exact sum_congr rfl fun k hk ↦ (weightedDiscrepancy_integralmulsum c hf hf_int _ _ _ (mod_cast k.le_succ)
      le_rfl (mod_cast le_rfl) (weightedDiscrepancy_ineqofmemIco' hk).1 <| mod_cast (weightedDiscrepancy_ineqofmemIco' hk).2)
  rw [this, sum_integral_adjacent_intervals_Ico hb, Nat.cast_add, Nat.cast_one,
    ← integral_interval_sub_left (a := a) (c := ⌊a⌋₊ + 1),
    ← integral_add_adjacent_intervals (b := ⌊b⌋₊) (c := b),
    weightedDiscrepancy_integralmulsum c hf hf_int _ _ _ aux3 aux1 le_rfl le_rfl aux4,
    weightedDiscrepancy_integralmulsum c hf hf_int _ _ _ aux5 le_rfl aux2 aux6 le_rfl]
  · ring
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le aux6]
    exact (integrableOn_mul_sum_Icc c ha hf_int).mono_set (Set.Icc_subset_Icc_right aux5)
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le aux5]
    exact (integrableOn_mul_sum_Icc c ha hf_int).mono_set (Set.Icc_subset_Icc_left aux6)
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le aux6]
    exact (integrableOn_mul_sum_Icc c ha hf_int).mono_set (Set.Icc_subset_Icc_right aux5)
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le aux3]
    exact (integrableOn_mul_sum_Icc c ha hf_int).mono_set (Set.Icc_subset_Icc_right aux4)
  · exact fun k hk ↦ (intervalIntegrable_iff_integrableOn_Icc_of_le (mod_cast k.le_succ)).mpr
      <| (integrableOn_mul_sum_Icc c ha hf_int).mono_set
        <| (Set.Icc_subset_Icc_iff (mod_cast k.le_succ)).mpr <| mod_cast (weightedDiscrepancy_ineqofmemIco hk)


end RealAbel

/-- The cutoff has exactly the source's open-left, closed-right normalization. -/
theorem weightedDiscrepancy_cutoff_prefix {E : Type*} [AddCommMonoid E]
    (c : ℕ → E) (m n : ℕ) :
    (∑ k ∈ Icc 0 n, if m < k then c k else 0) = ∑ k ∈ Ioc m n, c k := by
  classical
  have he : (Icc 0 n).filter (fun k => m < k) = Ioc m n := by
    ext k
    simp only [mem_filter, mem_Icc, mem_Ioc]
    omega
  rw [← he, sum_filter]

/-- Centered Abel identity, valid for absolutely continuous real weights. -/
theorem weightedDiscrepancy_real_centered_abel (c : ℕ → ℝ) {f : ℝ → ℝ}
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b) :
    (∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k * c k) =
      f b * (∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, c k) -
        ∫ t in a..b, deriv f t * ∑ k ∈ Ioc ⌊a⌋₊ ⌊t⌋₊, c k := by
  let d : ℕ → ℝ := fun k => if ⌊a⌋₊ < k then c k else 0
  have hi : IntegrableOn (deriv f) (Set.Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hf.intervalIntegrable_deriv
  have he := weightedDiscrepancy_real_abel d ha hab hf hi
  rw [← intervalIntegral.integral_of_le hab] at he
  simp only [d, weightedDiscrepancy_cutoff_prefix, Ioc_self, sum_empty,
    mul_zero, sub_zero] at he
  convert he using 1
  apply sum_congr rfl
  intro k hk
  rw [ite_eq_left (mem_Ioc.mp hk).1]

/-- Continuous integration by parts against an integrable real density. -/
theorem weightedDiscrepancy_real_density_parts {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : IntervalIntegrable g volume a b) :
    (∫ t in a..b, f t * g t) = f b * (∫ t in a..b, g t) -
      ∫ t in a..b, deriv f t * (∫ y in a..t, g y) := by
  have hG := hg.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
  have hp := hf.integral_mul_deriv_eq_deriv_mul hG
  have he : (∫ t in a..b, f t * deriv (fun x => ∫ y in a..x, g y) t) =
      ∫ t in a..b, f t * g t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hg.ae_hasDerivAt_integral] with t ht htmem
    rw [(ht (Set.uIoc_subset_uIcc htmem) a (by simp)).deriv]
  simpa only [he, intervalIntegral.integral_same, mul_zero, sub_zero] using hp

/-- The exact signed error is a boundary error minus an integral of prefix errors. -/
theorem weightedDiscrepancy_real_identity (c : ℕ → ℝ) {f g : ℝ → ℝ}
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : IntervalIntegrable g volume a b) :
    (∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k * c k) - (∫ t in a..b, f t * g t) =
      f b * ((∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, c k) - ∫ t in a..b, g t) -
        ∫ t in a..b, deriv f t *
          ((∑ k ∈ Ioc ⌊a⌋₊ ⌊t⌋₊, c k) - ∫ y in a..t, g y) := by
  have hd := hf.intervalIntegrable_deriv
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hd
  have hP : IntervalIntegrable
      (fun t => deriv f t * ∑ k ∈ Ioc ⌊a⌋₊ ⌊t⌋₊, c k) volume a b := by
    have h := integrableOn_mul_sum_Icc (m := 0)
      (fun k => if ⌊a⌋₊ < k then c k else 0) ha hi
    simp only [weightedDiscrepancy_cutoff_prefix] at h
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr h
  have hG := hg.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
  have hD := hd.mul_continuousOn hG.continuousOn
  rw [weightedDiscrepancy_real_centered_abel c ha hab hf,
    weightedDiscrepancy_real_density_parts hf hg]
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub hP hD]
  ring


/-- Uniform sharp-prefix error transfers to every real Lipschitz weight. -/
theorem weightedIntervalDiscrepancy_real_bound (c : ℕ → ℝ) (f g : ℝ → ℝ)
    {a b E : ℝ} {K : ℝ≥0} (ha : 0 ≤ a) (hab : a ≤ b) (_hE : 0 ≤ E)
    (hLip : LipschitzOnWith K f (Set.Icc a b))
    (hg : IntervalIntegrable g volume a b)
    (hprefix : ∀ t ∈ Set.Icc a b,
      ‖(∑ k ∈ Ioc ⌊a⌋₊ ⌊t⌋₊, c k) - ∫ y in a..t, g y‖ ≤ E) :
    ‖(∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k * c k) - ∫ t in a..b, f t * g t‖ ≤
      E * (‖f b‖ + (K : ℝ) * (b-a)) := by
  have hf : AbsolutelyContinuousOnInterval f a b :=
    (show LipschitzOnWith K f (Set.uIcc a b) by
      simpa only [Set.uIcc_of_le hab] using hLip).absolutelyContinuousOnInterval
  have hder : ∀ᵐ t, t ∈ Set.uIoc a b → ‖deriv f t‖ ≤ (K : ℝ) := by
    have hb : ∀ᵐ t : ℝ, t ≠ b := by simp [ae_iff, measure_singleton]
    filter_upwards [hb] with t htb ht
    rw [Set.uIoc_of_le hab] at ht
    exact norm_deriv_le_of_lipschitzOn
      (Icc_mem_nhds ht.1 (lt_of_le_of_ne ht.2 htb)) hLip
  have hint : ‖∫ t in a..b, deriv f t *
      ((∑ k ∈ Ioc ⌊a⌋₊ ⌊t⌋₊, c k) - ∫ y in a..t, g y)‖ ≤
      (K : ℝ) * E * (b-a) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const_ae
      (a := a) (b := b) (C := (K : ℝ)*E) (f := fun t => deriv f t *
        ((∑ k ∈ Ioc ⌊a⌋₊ ⌊t⌋₊, c k) - ∫ y in a..t, g y))
      (by
        filter_upwards [hder] with t ht hmem
        rw [norm_mul]
        exact mul_le_mul (ht hmem)
          (hprefix t (Set.uIcc_of_le hab ▸ Set.uIoc_subset_uIcc hmem))
          (norm_nonneg _) (NNReal.coe_nonneg K))
    simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using h
  rw [weightedDiscrepancy_real_identity c ha hab hf hg]
  calc
    _ ≤ ‖f b * ((∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, c k) - ∫ t in a..b, g t)‖ +
        ‖∫ t in a..b, deriv f t *
          ((∑ k ∈ Ioc ⌊a⌋₊ ⌊t⌋₊, c k) - ∫ y in a..t, g y)‖ := norm_sub_le _ _
    _ ≤ ‖f b‖ * E + (K : ℝ) * E * (b-a) := by
      rw [norm_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left
        (hprefix b ⟨hab,le_rfl⟩) (norm_nonneg _)) hint
    _ = _ := by ring

theorem weightedDiscrepancy_integral_re {g : ℝ → ℂ} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) :
    (∫ t in a..b, (g t).re) = (∫ t in a..b, g t).re :=
  Complex.reCLM.intervalIntegral_comp_comm hg

theorem weightedDiscrepancy_integral_im {g : ℝ → ℂ} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) :
    (∫ t in a..b, (g t).im) = (∫ t in a..b, g t).im :=
  Complex.imCLM.intervalIntegral_comp_comm hg

/-- Real Lipschitz weights against complex discrete and continuous measures. -/
theorem weightedIntervalDiscrepancy_real_weight_bound (c : ℕ → ℂ)
    (f : ℝ → ℝ) (g : ℝ → ℂ) {a b E : ℝ} {K : ℝ≥0}
    (ha : 0 ≤ a) (hab : a ≤ b) (hE : 0 ≤ E)
    (hLip : LipschitzOnWith K f (Set.Icc a b))
    (hg : IntervalIntegrable g volume a b)
    (hprefix : ∀ t ∈ Set.Icc a b,
      ‖(∑ k ∈ Ioc ⌊a⌋₊ ⌊t⌋₊, c k) - ∫ y in a..t, g y‖ ≤ E) :
    ‖(∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (f k : ℂ) * c k) -
        ∫ t in a..b, (f t : ℂ) * g t‖ ≤
      2 * E * (‖f b‖ + (K : ℝ) * (b-a)) := by
  have hgR : IntervalIntegrable (fun t => (g t).re) volume a b :=
    ⟨Complex.reCLM.integrable_comp hg.1, Complex.reCLM.integrable_comp hg.2⟩
  have hgI : IntervalIntegrable (fun t => (g t).im) volume a b :=
    ⟨Complex.imCLM.integrable_comp hg.1, Complex.imCLM.integrable_comp hg.2⟩
  have hgt (t : ℝ) (ht : t ∈ Set.Icc a b) : IntervalIntegrable g volume a t := by
    apply hg.mono_set
    rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc le_rfl ht.2
  have hprefixR : ∀ t ∈ Set.Icc a b,
      ‖(∑ k ∈ Ioc ⌊a⌋₊ ⌊t⌋₊, (c k).re) - ∫ y in a..t, (g y).re‖ ≤ E := by
    intro t ht
    have he := Complex.abs_re_le_norm
      ((∑ k ∈ Ioc ⌊a⌋₊ ⌊t⌋₊, c k) - ∫ y in a..t, g y)
    rw [Complex.sub_re, Complex.re_sum, ← weightedDiscrepancy_integral_re (hgt t ht)] at he
    exact he.trans (hprefix t ht)
  have hprefixI : ∀ t ∈ Set.Icc a b,
      ‖(∑ k ∈ Ioc ⌊a⌋₊ ⌊t⌋₊, (c k).im) - ∫ y in a..t, (g y).im‖ ≤ E := by
    intro t ht
    have he := Complex.abs_im_le_norm
      ((∑ k ∈ Ioc ⌊a⌋₊ ⌊t⌋₊, c k) - ∫ y in a..t, g y)
    rw [Complex.sub_im, Complex.im_sum, ← weightedDiscrepancy_integral_im (hgt t ht)] at he
    exact he.trans (hprefix t ht)
  have hR := weightedIntervalDiscrepancy_real_bound (fun k => (c k).re)
    f (fun t => (g t).re) ha hab hE hLip hgR hprefixR
  have hI := weightedIntervalDiscrepancy_real_bound (fun k => (c k).im)
    f (fun t => (g t).im) ha hab hE hLip hgI hprefixI
  have hfc : ContinuousOn (fun t => (f t : ℂ)) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact Complex.continuous_ofReal.comp_continuousOn hLip.continuousOn
  have hfg := hg.continuousOn_mul hfc
  let z : ℂ := (∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (f k : ℂ) * c k) -
    ∫ t in a..b, (f t : ℂ) * g t
  have hzR : z.re = (∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k * (c k).re) -
      ∫ t in a..b, f t * (g t).re := by
    dsimp only [z]
    rw [Complex.sub_re, Complex.re_sum, ← weightedDiscrepancy_integral_re hfg]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hzI : z.im = (∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k * (c k).im) -
      ∫ t in a..b, f t * (g t).im := by
    dsimp only [z]
    rw [Complex.sub_im, Complex.im_sum, ← weightedDiscrepancy_integral_im hfg]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  change ‖z‖ ≤ _
  calc
    _ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ E * (‖f b‖ + (K : ℝ) * (b-a)) + E * (‖f b‖ + (K : ℝ) * (b-a)) := by
      rw [hzR, hzI]
      exact add_le_add hR hI
    _ = _ := by ring


/-- Lipschitz transport from unweighted sharp-prefix discrepancy to a weighted
finite sum minus the actual continuous-density integral. -/
theorem weightedIntervalDiscrepancy_bound (c : ℕ → ℂ) (φ g : ℝ → ℂ)
    {a b E : ℝ} {K : ℝ≥0} (ha : 0 ≤ a) (hab : a ≤ b) (hE : 0 ≤ E)
    (hLip : LipschitzOnWith K φ (Set.Icc a b))
    (hg : IntervalIntegrable g volume a b)
    (hprefix : ∀ t ∈ Set.Icc a b,
      ‖(∑ k ∈ Ioc ⌊a⌋₊ ⌊t⌋₊, c k) - ∫ y in a..t, g y‖ ≤ E) :
    ‖(∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, φ k * c k) - ∫ t in a..b, φ t * g t‖ ≤
      4 * E * (‖φ b‖ + (K : ℝ) * (b-a)) := by
  have hLipR : LipschitzOnWith K (fun t => (φ t).re) (Set.Icc a b) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    change |(φ x).re - (φ y).re| ≤ (K : ℝ) * |x-y|
    calc
      _ = |(φ x - φ y).re| := by rw [Complex.sub_re]
      _ ≤ ‖φ x - φ y‖ := Complex.abs_re_le_norm _
      _ ≤ _ := by simpa only [dist_eq_norm, Real.norm_eq_abs] using hLip.dist_le_mul x hx y hy
  have hLipI : LipschitzOnWith K (fun t => (φ t).im) (Set.Icc a b) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    change |(φ x).im - (φ y).im| ≤ (K : ℝ) * |x-y|
    calc
      _ = |(φ x - φ y).im| := by rw [Complex.sub_im]
      _ ≤ ‖φ x - φ y‖ := Complex.abs_im_le_norm _
      _ ≤ _ := by simpa only [dist_eq_norm, Real.norm_eq_abs] using hLip.dist_le_mul x hx y hy
  have hR := weightedIntervalDiscrepancy_real_weight_bound c (fun t => (φ t).re) g
    ha hab hE hLipR hg hprefix
  have hI := weightedIntervalDiscrepancy_real_weight_bound c (fun t => (φ t).im) g
    ha hab hE hLipI hg hprefix
  let R : ℂ := (∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, ((φ k).re : ℂ) * c k) -
    ∫ t in a..b, ((φ t).re : ℂ) * g t
  let J : ℂ := (∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, ((φ k).im : ℂ) * c k) -
    ∫ t in a..b, ((φ t).im : ℂ) * g t
  have hφ (t : ℝ) : φ t = ((φ t).re : ℂ) + Complex.I * ((φ t).im : ℂ) := by
    apply Complex.ext <;> simp
  have hsum : (∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, φ k * c k) =
      (∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, ((φ k).re : ℂ) * c k) +
      Complex.I * (∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, ((φ k).im : ℂ) * c k) := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    nth_rw 1 [hφ k]
    ring
  have hc : ContinuousOn φ (Set.uIcc a b) := by
    simpa only [Set.uIcc_of_le hab] using hLip.continuousOn
  have hgR : IntervalIntegrable (fun t => ((φ t).re : ℂ) * g t) volume a b :=
    hg.continuousOn_mul (Complex.continuous_ofReal.comp_continuousOn
      (Complex.continuous_re.comp_continuousOn hc))
  have hgI : IntervalIntegrable (fun t => ((φ t).im : ℂ) * g t) volume a b :=
    hg.continuousOn_mul (Complex.continuous_ofReal.comp_continuousOn
      (Complex.continuous_im.comp_continuousOn hc))
  have hint : (∫ t in a..b, φ t * g t) =
      (∫ t in a..b, ((φ t).re : ℂ) * g t) +
      Complex.I * (∫ t in a..b, ((φ t).im : ℂ) * g t) := by
    calc
      _ = ∫ t in a..b, ((φ t).re : ℂ) * g t +
          Complex.I * (((φ t).im : ℂ) * g t) := by
        apply intervalIntegral.integral_congr
        intro t _
        dsimp only
        nth_rw 1 [hφ t]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add hgR (hgI.const_mul Complex.I),
          intervalIntegral.integral_const_mul]
  have he : (∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, φ k * c k) - ∫ t in a..b, φ t * g t =
      R + Complex.I * J := by
    rw [hsum, hint]
    dsimp only [R, J]
    ring
  have hR' : ‖R‖ ≤ 2*E*(‖φ b‖ + (K : ℝ)*(b-a)) := by
    exact hR.trans (mul_le_mul_of_nonneg_left
      (add_le_add (Complex.abs_re_le_norm (φ b)) le_rfl) (by positivity))
  have hI' : ‖J‖ ≤ 2*E*(‖φ b‖ + (K : ℝ)*(b-a)) := by
    exact hI.trans (mul_le_mul_of_nonneg_left
      (add_le_add (Complex.abs_im_le_norm (φ b)) le_rfl) (by positivity))
  rw [he]
  calc
    _ ≤ ‖R‖ + ‖Complex.I * J‖ := norm_add_le _ _
    _ = ‖R‖ + ‖J‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    _ ≤ 2*E*(‖φ b‖ + (K : ℝ)*(b-a)) + 2*E*(‖φ b‖ + (K : ℝ)*(b-a)) :=
      add_le_add hR' hI'
    _ = _ := by ring

end
end ArtinMatthews
