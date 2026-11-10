module

public import ArtinMatthews.L2MeasurableCutoff
public import Mathlib.MeasureTheory.Function.L2Space


set_option backward.privateInPublic true
@[expose] public section

/-! L2 restriction estimates under explicit domination by a chart measure. -/
namespace ArtinMatthews
open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable (μ : Measure X) (ν ρ : Measure Y)

theorem chart_lintegral_le (S : Set X) (hS : MeasurableSet S)
    (q : Y → X) (hq : Measurable q) (C : ℝ≥0∞)
    (hμ : μ.restrict S ≤ C • Measure.map q ρ)
    (h : X → ℝ≥0∞) (H : Y → ℝ≥0∞)
    (hH : ∀ᵐ y ∂ρ, q y ∈ S → h (q y) ≤ H y) :
    ∫⁻ x in S, h x ∂μ ≤ C * ∫⁻ y, H y ∂ρ := by
  calc
    _ = ∫⁻ x, S.indicator h x ∂μ.restrict S := by
      rw [lintegral_indicator hS, Measure.restrict_restrict hS, inter_self]
    _ ≤ ∫⁻ x, S.indicator h x ∂(C • Measure.map q ρ) :=
      lintegral_mono' hμ le_rfl
    _ = C * ∫⁻ x, S.indicator h x ∂Measure.map q ρ := by
      rw [lintegral_smul_measure, smul_eq_mul]
    _ ≤ C * ∫⁻ y, S.indicator h (q y) ∂ρ :=
      mul_le_mul_right (lintegral_map_le _ hq.aemeasurable) C
    _ ≤ _ := by
      apply mul_le_mul_right
      apply lintegral_mono_ae
      filter_upwards [hH] with y hy
      by_cases hqy : q y ∈ S
      · simpa only [indicator_of_mem hqy] using hy hqy
      · simp only [indicator_of_notMem hqy, zero_le]

theorem heightL2_norm_sq_lintegral (f : HeightL2 μ) :
    ENNReal.ofReal (‖f‖ ^ 2) = ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ := by
  rw [heightL2_norm_sq_integral μ]
  exact ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f))
    (Eventually.of_forall fun _ => sq_nonneg _)

theorem measurableL2Cutoff_dist_sq_lintegral (S : Set X) (hS : MeasurableSet S)
    (f g : HeightL2 μ) :
    ENNReal.ofReal (dist (measurableL2Cutoff μ S hS f)
      (measurableL2Cutoff μ S hS g) ^ 2) =
        ∫⁻ x in S, ENNReal.ofReal (‖f x - g x‖ ^ 2) ∂μ := by
  rw [dist_eq_norm, ← map_sub, measurableL2Cutoff_norm_sq μ]
  have hi := ((memLp_two_iff_integrable_sq_norm
    (Lp.aestronglyMeasurable (f - g))).mp (Lp.memLp (f - g))).restrict (s := S)
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => sq_nonneg _)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub f g)] with x hx
  rw [hx]
  rfl

theorem l2_chart_cutoff_dist_sq_le (hρν : ρ ≤ ν)
    (S : Set X) (hS : MeasurableSet S) (q : Y → X) (hq : Measurable q)
    (C : ℝ) (hC : 0 ≤ C)
    (hμ : μ.restrict S ≤ ENNReal.ofReal C • Measure.map q ρ)
    (f g : HeightL2 μ) (F G : HeightL2 ν)
    (hf : ∀ᵐ y ∂ρ, q y ∈ S → f (q y) = F y)
    (hg : ∀ᵐ y ∂ρ, q y ∈ S → g (q y) = G y) :
    dist (measurableL2Cutoff μ S hS f) (measurableL2Cutoff μ S hS g) ^ 2 ≤
      C * dist F G ^ 2 := by
  have hbound : ENNReal.ofReal (dist (measurableL2Cutoff μ S hS f)
      (measurableL2Cutoff μ S hS g) ^ 2) ≤ ENNReal.ofReal (C * dist F G ^ 2) := by
    rw [measurableL2Cutoff_dist_sq_lintegral μ S hS]
    calc
      _ ≤ ENNReal.ofReal C * ∫⁻ y, ENNReal.ofReal (‖(F - G) y‖ ^ 2) ∂ρ := by
        apply chart_lintegral_le μ ρ S hS q hq _ hμ
        filter_upwards [hf, hg, (ae_mono hρν) (Lp.coeFn_sub F G)] with y hfy hgy hsub
        intro hy
        rw [hfy hy, hgy hy, hsub]
        rfl
      _ ≤ ENNReal.ofReal C * ∫⁻ y, ENNReal.ofReal (‖(F - G) y‖ ^ 2) ∂ν :=
        mul_le_mul_right (lintegral_mono' hρν le_rfl) _
      _ = _ := by
        rw [← heightL2_norm_sq_lintegral ν, ENNReal.ofReal_mul hC, dist_eq_norm]
  have ht := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hbound
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _),
    ENNReal.toReal_ofReal (mul_nonneg hC (sq_nonneg _))] using ht

theorem l2_chart_cutoff_dist_le (hρν : ρ ≤ ν)
    (S : Set X) (hS : MeasurableSet S) (q : Y → X) (hq : Measurable q)
    (C : ℝ) (hC : 0 ≤ C)
    (hμ : μ.restrict S ≤ ENNReal.ofReal C • Measure.map q ρ)
    (f g : HeightL2 μ) (F G : HeightL2 ν)
    (hf : ∀ᵐ y ∂ρ, q y ∈ S → f (q y) = F y)
    (hg : ∀ᵐ y ∂ρ, q y ∈ S → g (q y) = G y) :
    dist (measurableL2Cutoff μ S hS f) (measurableL2Cutoff μ S hS g) ≤
      Real.sqrt C * dist F G := by
  have hs := l2_chart_cutoff_dist_sq_le μ ν ρ hρν S hS q hq C hC hμ f g F G hf hg
  have hsq := Real.sq_sqrt hC
  have hn := mul_nonneg (Real.sqrt_nonneg C) (dist_nonneg (x := F) (y := G))
  nlinarith [dist_nonneg (x := measurableL2Cutoff μ S hS f)
    (y := measurableL2Cutoff μ S hS g), sq_nonneg
      (dist (measurableL2Cutoff μ S hS f) (measurableL2Cutoff μ S hS g) -
        Real.sqrt C * dist F G)]

end
end ArtinMatthews
