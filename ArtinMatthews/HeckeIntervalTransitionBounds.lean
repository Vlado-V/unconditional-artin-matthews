module

public import ArtinMatthews.HeckeIntervalCutoff
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Quantitative smooth interval transitions in the actual logarithmic variable. -/

namespace ArtinMatthews
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

def heckeIntervalTransition (s : ℝ) : ℂ := Real.smoothTransition s

theorem heckeIntervalTransition_contDiff : ContDiff ℝ ∞ heckeIntervalTransition :=
  Complex.ofRealCLM.contDiff.comp Real.smoothTransition.contDiff

theorem heckeIntervalTransition_derivative_zero_outside (j : ℕ) {s : ℝ}
    (hs : s ∉ Icc (0 : ℝ) 1) :
    iteratedDeriv (j + 1) heckeIntervalTransition s = 0 := by
  rcases not_and_or.mp hs with hleft | hright
  · have hlt : s < 0 := lt_of_not_ge hleft
    have he : heckeIntervalTransition =ᶠ[𝓝 s] (fun _ => (0 : ℂ)) := by
      filter_upwards [isOpen_Iio.mem_nhds hlt] with t ht
      simp only [heckeIntervalTransition, Real.smoothTransition.zero_of_nonpos ht.le,
        Complex.ofReal_zero]
    rw [he.iteratedDeriv_eq (j + 1)]
    simp only [iteratedDeriv_const, Nat.add_one_ne_zero, ite_false]
  · have hlt : 1 < s := lt_of_not_ge hright
    have he : heckeIntervalTransition =ᶠ[𝓝 s] (fun _ => (1 : ℂ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hlt] with t ht
      simp only [heckeIntervalTransition, Real.smoothTransition.one_of_one_le ht.le,
        Complex.ofReal_one]
    rw [he.iteratedDeriv_eq (j + 1)]
    simp only [iteratedDeriv_const, Nat.add_one_ne_zero, ite_false]

/-- Every derivative of the literal smooth transition is bounded globally. -/
theorem heckeIntervalTransition_derivative_bound (j : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ s : ℝ, ‖iteratedDeriv j heckeIntervalTransition s‖ ≤ D := by
  cases j with
  | zero =>
    refine ⟨1, by norm_num, fun s => ?_⟩
    rw [iteratedDeriv_zero, heckeIntervalTransition, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.smoothTransition.nonneg s)]
    exact Real.smoothTransition.le_one s
  | succ j =>
    have hc : Continuous (iteratedDeriv (j + 1) heckeIntervalTransition) :=
      ContDiff.continuous_iteratedDeriv (j + 1) heckeIntervalTransition_contDiff (by simp)
    obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
      hc.continuousOn
    refine ⟨|M| + 1, by positivity, fun s => ?_⟩
    by_cases hs : s ∈ Icc (0 : ℝ) 1
    · exact (hM s hs).trans (by linarith [le_abs_self M])
    · rw [heckeIntervalTransition_derivative_zero_outside j hs, norm_zero]
      positivity

/-- Exact reciprocal-scale normalization, including the moving endpoint. -/
theorem heckeIntervalTransition_scaled_derivative (j : ℕ) (ε u s : ℝ) :
    iteratedDeriv j (fun t => heckeIntervalTransition ((t-u)/ε)) s =
      (ε⁻¹)^j • iteratedDeriv j heckeIntervalTransition ((s-u)/ε) := by
  have hshift := congrFun
    (iteratedDeriv_comp_sub_const j (fun t => heckeIntervalTransition (t/ε)) u) s
  have hscale := congrFun (iteratedDeriv_comp_const_smul
    (heckeIntervalTransition_contDiff.of_le (by simp) : ContDiff ℝ j heckeIntervalTransition)
    ε⁻¹) (s-u)
  simp only [div_eq_mul_inv, mul_comm] at hshift hscale ⊢
  exact hshift.trans hscale

/-- Actual derivative bounds for the moving interval profile; the endpoints
do not enter the constants. -/
theorem heckeLogIntervalProfile_derivative_bound (j : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ ε : ℝ, 0 < ε → ∀ u v s : ℝ,
      ‖iteratedDeriv j (heckeLogIntervalProfile ε u v) s‖ ≤ D * (ε⁻¹)^j := by
  obtain ⟨M, hM, hb⟩ := heckeIntervalTransition_derivative_bound j
  refine ⟨2 * M, by positivity, fun ε hε u v s => ?_⟩
  have he : heckeLogIntervalProfile ε u v =
      (fun t => heckeIntervalTransition ((t-u)/ε)) -
        (fun t => heckeIntervalTransition ((t-v)/ε)) := by
    funext t
    simp only [heckeLogIntervalProfile, heckeIntervalTransition, Pi.sub_apply,
      Complex.ofReal_sub]
  have hu : ContDiff ℝ ∞ (fun t => heckeIntervalTransition ((t-u)/ε)) :=
    heckeIntervalTransition_contDiff.comp ((contDiff_id.sub contDiff_const).div_const ε)
  have hv : ContDiff ℝ ∞ (fun t => heckeIntervalTransition ((t-v)/ε)) :=
    heckeIntervalTransition_contDiff.comp ((contDiff_id.sub contDiff_const).div_const ε)
  rw [he, iteratedDeriv_sub (hu.of_le (by simp)).contDiffAt (hv.of_le (by simp)).contDiffAt,
    heckeIntervalTransition_scaled_derivative, heckeIntervalTransition_scaled_derivative]
  calc
    _ ≤ ‖(ε⁻¹)^j • iteratedDeriv j heckeIntervalTransition ((s-u)/ε)‖ +
        ‖(ε⁻¹)^j • iteratedDeriv j heckeIntervalTransition ((s-v)/ε)‖ := norm_sub_le _ _
    _ ≤ (ε⁻¹)^j * M + (ε⁻¹)^j * M := by
      simp only [norm_smul, norm_pow, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε)]
      exact add_le_add (mul_le_mul_of_nonneg_left (hb _) (by positivity))
        (mul_le_mul_of_nonneg_left (hb _) (by positivity))
    _ = _ := by ring

theorem heckeLogIntervalProfile_reflected_derivative_bound (j : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ ε : ℝ, 0 < ε → ∀ u v s : ℝ,
      ‖iteratedDeriv j (fun t => heckeLogIntervalProfile ε u v (-t)) s‖ ≤ D * (ε⁻¹)^j := by
  obtain ⟨D, hD, hb⟩ := heckeLogIntervalProfile_derivative_bound j
  refine ⟨D, hD, fun ε hε u v s => ?_⟩
  rw [iteratedDeriv_comp_neg, norm_smul, norm_pow]
  simpa only [norm_neg, norm_one, one_pow, one_mul] using hb ε hε u v (-s)

theorem heckeInterval_section_deriv_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ → ℂ) (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun p : E × ℝ => deriv (F p.1) p.2) := by
  have hFp : ContDiff ℝ ∞ (Function.uncurry (fun p : E × ℝ => F p.1)) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd := hFp.fderiv contDiff_snd (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  simpa only [deriv] using hd.clm_apply (contDiff_const (c := (1 : ℝ)))

theorem heckeInterval_section_iteratedDeriv_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ → ℂ) (hF : ContDiff ℝ ∞ (Function.uncurry F)) (j : ℕ) :
    ContDiff ℝ ∞ (fun p : E × ℝ => iteratedDeriv j (F p.1) p.2) := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero, Function.uncurry_def] using hF
  | succ j ih =>
    simpa only [iteratedDeriv_succ] using
      heckeInterval_section_deriv_smooth (fun p => iteratedDeriv j (F p)) ih

def heckeLogIntervalFixedSupport : Set ℝ := Icc (-Real.log 2 - 1) 0

/-- Joint smoothness gives actual uniform amplitude bounds on the compact
parameter set and fixed logarithmic support. -/
theorem heckeInterval_amplitude_derivative_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ → ℂ) (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (J : Set E) (hJ : IsCompact J) (j : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ p ∈ J, ∀ s ∈ heckeLogIntervalFixedSupport,
      ‖iteratedDeriv j (F p) s‖ ≤ M := by
  obtain ⟨M, hM⟩ := (hJ.prod (isCompact_Icc : IsCompact heckeLogIntervalFixedSupport)).exists_bound_of_continuousOn
    (heckeInterval_section_iteratedDeriv_smooth F hF j).continuous.continuousOn
  exact ⟨|M| + 1, by positivity, fun p hp s hs =>
    (hM (p, s) ⟨hp, hs⟩).trans (by linarith [le_abs_self M])⟩

theorem heckeInterval_iteratedDeriv_tsupport (F : ℝ → ℂ) (j : ℕ) :
    tsupport (iteratedDeriv j F) ⊆ tsupport F := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

theorem heckeLogIntervalProfile_amplitude_tsupport (F : ℝ → ℂ)
    {ε u v : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ Real.log 2) :
    tsupport (fun s => F s * heckeLogIntervalProfile ε u v (-s)) ⊆
      heckeLogIntervalFixedSupport := by
  apply closure_minimal _ isClosed_Icc
  intro s hs
  have hprofile : heckeLogIntervalProfile ε u v (-s) ≠ 0 := right_ne_zero_of_mul hs
  have hb := heckeLogIntervalProfile_support hε huv hprofile
  exact ⟨by linarith [hb.2], by linarith [hb.1]⟩

/-- In particular, all the actual log derivatives are absolutely integrable. -/
theorem heckeLogIntervalProfile_amplitude_derivative_integrable
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (j : ℕ)
    {ε u v : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ Real.log 2) :
    Integrable (iteratedDeriv j (fun s => F s * heckeLogIntervalProfile ε u v (-s))) := by
  have hs : tsupport (iteratedDeriv j (fun s => F s * heckeLogIntervalProfile ε u v (-s))) ⊆
      heckeLogIntervalFixedSupport :=
    (heckeInterval_iteratedDeriv_tsupport _ j).trans
      (heckeLogIntervalProfile_amplitude_tsupport F hε hε1 hu huv hv)
  have hc : HasCompactSupport (iteratedDeriv j (fun s => F s * heckeLogIntervalProfile ε u v (-s))) :=
    (isCompact_Icc : IsCompact heckeLogIntervalFixedSupport).of_isClosed_subset (isClosed_tsupport _) hs
  have hsm : ContDiff ℝ ∞ (fun s => F s * heckeLogIntervalProfile ε u v (-s)) :=
    hF.mul ((heckeLogIntervalProfile_smooth ε u v).comp contDiff_id.neg)
  exact (ContDiff.continuous_iteratedDeriv j hsm (by simp)).integrable_of_hasCompactSupport hc

/-- The constants depend only on the actual fixed smooth amplitude family,
its compact parameter set, and the derivative order.  The moving interval
endpoints and transition width do not enter the constants. -/
theorem heckeLogIntervalProfile_amplitude_derivative_L1_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ → ℂ) (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (J : Set E) (hJ : IsCompact J) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ J, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ Real.log 2 →
      (∫ s : ℝ, ‖iteratedDeriv j (fun t => F p t * heckeLogIntervalProfile ε u v (-t)) s‖) ≤
        C / ε^j := by
  choose M hM hMb using fun i : ℕ => heckeInterval_amplitude_derivative_bound F hF J hJ i
  choose D hD hDb using heckeLogIntervalProfile_reflected_derivative_bound
  let T : ℝ := ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * M i * D (j-i)
  have hT : 0 ≤ T := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hM i).le) (hD (j-i)).le)
  let C₀ : ℝ := T + 1
  have hC₀ : 0 < C₀ := by dsimp [C₀]; linarith
  refine ⟨C₀ * (volume.real heckeLogIntervalFixedSupport + 1), by positivity,
    fun p hp ε hε hε1 u v hu huv hv => ?_⟩
  have hεinv : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).mpr hε1
  have hFp : ContDiff ℝ ∞ (F p) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hprofile : ContDiff ℝ ∞ (fun t => heckeLogIntervalProfile ε u v (-t)) :=
    (heckeLogIntervalProfile_smooth ε u v).comp contDiff_id.neg
  have hpoint : ∀ s ∈ heckeLogIntervalFixedSupport,
      ‖iteratedDeriv j (fun t => F p t * heckeLogIntervalProfile ε u v (-t)) s‖ ≤ C₀ * (ε⁻¹)^j := by
    intro s hs
    have hb := norm_iteratedFDeriv_mul_le hFp hprofile s (n := j) (by simp)
    simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hb
    calc
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedDeriv i (F p) s‖ *
          ‖iteratedDeriv (j-i) (fun t => heckeLogIntervalProfile ε u v (-t)) s‖ := hb
      _ ≤ ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * M i * D (j-i) * (ε⁻¹)^j := by
        apply Finset.sum_le_sum
        intro i _
        have hMi : 0 < M i := hM i
        have hDi : 0 < D (j-i) := hD (j-i)
        have hd := hDb (j-i) ε hε u v s
        have hpow := pow_le_pow_right₀ hεinv (Nat.sub_le j i)
        calc
          _ ≤ (j.choose i : ℝ) * M i * (D (j-i) * (ε⁻¹)^(j-i)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hMb i p hp s hs) (by positivity))
              hd (norm_nonneg _) (by positivity)
          _ ≤ (j.choose i : ℝ) * M i * (D (j-i) * (ε⁻¹)^j) := by gcongr
          _ = _ := by ring
      _ = T * (ε⁻¹)^j := by rw [Finset.sum_mul]
      _ ≤ C₀ * (ε⁻¹)^j := by gcongr; dsimp [C₀]; linarith
  have hsupp : tsupport (iteratedDeriv j (fun t => F p t * heckeLogIntervalProfile ε u v (-t))) ⊆
      heckeLogIntervalFixedSupport :=
    (heckeInterval_iteratedDeriv_tsupport _ j).trans
      (heckeLogIntervalProfile_amplitude_tsupport (F p) hε hε1 hu huv hv)
  have hzero : ∀ s, s ∉ heckeLogIntervalFixedSupport →
      ‖iteratedDeriv j (fun t => F p t * heckeLogIntervalProfile ε u v (-t)) s‖ = 0 := by
    intro s hs
    have hz : iteratedDeriv j (fun t => F p t * heckeLogIntervalProfile ε u v (-t)) s = 0 := by
      by_contra hn
      exact hs (hsupp (subset_tsupport _ hn))
    rw [hz, norm_zero]
  have hi := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (f := fun s => ‖iteratedDeriv j (fun t => F p t * heckeLogIntervalProfile ε u v (-t)) s‖)
    (isCompact_Icc : IsCompact heckeLogIntervalFixedSupport).measure_lt_top
    (C := C₀ * (ε⁻¹)^j) (fun s hs => by simpa only [Real.norm_of_nonneg (norm_nonneg _)] using hpoint s hs)
  change ‖∫ s : ℝ in heckeLogIntervalFixedSupport,
      ‖iteratedDeriv j (fun t => F p t * heckeLogIntervalProfile ε u v (-t)) s‖‖ ≤
    C₀ * (ε⁻¹)^j * volume.real heckeLogIntervalFixedSupport at hi
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) hzero,
    Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] at hi
  calc
    _ ≤ C₀ * (ε⁻¹)^j * volume.real heckeLogIntervalFixedSupport := hi
    _ ≤ C₀ * (ε⁻¹)^j * (volume.real heckeLogIntervalFixedSupport + 1) := by gcongr; linarith
    _ = _ := by rw [div_eq_mul_inv, inv_pow]; ring

end
end ArtinMatthews
