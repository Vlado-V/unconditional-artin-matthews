module

public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! The source cutoff with its combined Mellin twist has uniformly
controlled total variation on the physical interval. -/
namespace ArtinMatthews
open Filter MeasureTheory
open scoped Topology
noncomputable section

def sourceComparisonMellinTest (ψ : ℝ → ℂ) (Y τ : ℝ) (w : ℝ) : ℂ :=
  ψ (w / Y) * Complex.exp (((τ * Real.log w : ℝ) : ℂ) * Complex.I)

theorem sourceComparisonMellinTest_eq_cpow (ψ : ℝ → ℂ) (Y τ : ℝ)
    {w : ℝ} (hw : 0 < w) :
    sourceComparisonMellinTest ψ Y τ w = ψ (w / Y) * (w : ℂ) ^ ((τ : ℂ) * Complex.I) := by
  unfold sourceComparisonMellinTest
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hw.ne'),
    ← Complex.ofReal_log hw.le, Complex.ofReal_mul]
  congr 2
  ring

theorem sourceComparisonMellinTest_norm (ψ : ℝ → ℂ) (Y τ w : ℝ) :
    ‖sourceComparisonMellinTest ψ Y τ w‖ = ‖ψ (w / Y)‖ := by
  rw [sourceComparisonMellinTest, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

private theorem mellinTest_eventually_zero (ψ : ℝ → ℂ) (Y τ a w : ℝ)
    (hψ : ∀ z < a, ψ z = 0) (hw : w / Y < a) :
    sourceComparisonMellinTest ψ Y τ =ᶠ[𝓝 w] (fun _ => 0) := by
  have h := (continuous_id.div_const Y).continuousAt.eventually (gt_mem_nhds hw)
  filter_upwards [h] with z hz
  exact mul_eq_zero_of_left (hψ (z / Y) hz) _

theorem sourceComparisonMellinTest_contDiff (ψ : ℝ → ℂ) {Y a : ℝ} (τ : ℝ)
    (ha : 0 < a) (hψ : ContDiff ℝ 1 ψ) (hs : ∀ z < a, ψ z = 0) :
    ContDiff ℝ 1 (sourceComparisonMellinTest ψ Y τ) := by
  rw [contDiff_iff_contDiffAt]
  intro w
  by_cases hw : w = 0
  · apply (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (0 : ℂ))).contDiffAt.congr_of_eventuallyEq
    exact mellinTest_eventually_zero ψ Y τ a w hs (by simpa [hw] using ha)
  · have hl : ContDiffAt ℝ 1 (fun z : ℝ => τ * Real.log z) w :=
      contDiffAt_const.mul (Real.contDiffAt_log.mpr hw)
    have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp w hl
    exact (hψ.contDiffAt.comp w (contDiffAt_id.div_const Y)).mul
      ((hc.mul contDiffAt_const).cexp)

theorem sourceComparisonMellinTest_variation (ψ : ℝ → ℂ) {Y a B M M₁ : ℝ} (τ : ℝ)
    (hY : 0 < Y) (ha : 0 < a) (hB : 0 ≤ B)
    (hM : 0 ≤ M) (hM₁ : 0 ≤ M₁) (hψ : ContDiff ℝ 1 ψ) (hs : ∀ z < a, ψ z = 0)
    (h0 : ∀ z, ‖ψ z‖ ≤ M) (h1 : ∀ z, ‖deriv ψ z‖ ≤ M₁) :
    (∫ w in Set.Ioc 0 (B * Y), ‖deriv (sourceComparisonMellinTest ψ Y τ) w‖) ≤
      B * (M₁ + M * |τ| / a) := by
  let F := sourceComparisonMellinTest ψ Y τ
  let C := (M₁ + M * |τ| / a) / Y
  have hC : 0 ≤ C := by unfold C; positivity
  have hFY : Continuous (fun w => ‖deriv F w‖) :=
    ((sourceComparisonMellinTest_contDiff ψ τ ha hψ hs).continuous_deriv (by norm_num)).norm
  have hbound (w : ℝ) (hw : w ∈ Set.Ioc 0 (B * Y)) : ‖deriv F w‖ ≤ C := by
    by_cases hw' : w / Y < a
    · have hz : F =ᶠ[𝓝 w] (fun _ => 0) := mellinTest_eventually_zero ψ Y τ a w hs hw'
      rw [Filter.EventuallyEq.deriv_eq hz, deriv_const, norm_zero]
      exact hC
    · have hw₀ : 0 < w := hw.1
      have hwa : a * Y ≤ w := (le_div_iff₀ hY).mp (le_of_not_gt hw')
      let ζ (z : ℝ) := Complex.exp (((τ * Real.log z : ℝ) : ℂ) * Complex.I)
      have hζ : ‖ζ w‖ = 1 := Complex.norm_exp_ofReal_mul_I _
      have hphase := (((Real.hasDerivAt_log hw₀.ne').const_mul τ).ofReal_comp.mul_const Complex.I).cexp
      have htest := ((hψ.differentiable (by norm_num) (w / Y)).hasDerivAt.scomp w
        ((hasDerivAt_id w).div_const Y)).mul hphase
      have hd : deriv F w =
          ((Y⁻¹ : ℝ) • deriv ψ (w / Y)) * ζ w +
            ψ (w / Y) * (ζ w * (((τ * w⁻¹ : ℝ) : ℂ) * Complex.I)) := by
        change HasDerivAt (sourceComparisonMellinTest ψ Y τ) _ w at htest
        simpa only [F, ζ, one_div, Function.comp_apply, id_eq] using htest.deriv
      have hYinv : 0 ≤ Y⁻¹ := inv_nonneg.mpr hY.le
      have hτ : ‖((τ * w⁻¹ : ℝ) : ℂ)‖ = |τ| / w := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hw₀, div_eq_mul_inv]
      rw [hd]
      apply (norm_add_le _ _).trans
      rw [norm_mul, norm_smul, hζ, mul_one, Real.norm_of_nonneg hYinv,
        norm_mul, norm_mul, norm_mul, hζ, one_mul, Complex.norm_I, mul_one, hτ]
      have hinv : |τ| / w ≤ |τ| / (a * Y) := div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos ha hY) hwa
      calc
        _ ≤ Y⁻¹ * M₁ + M * (|τ| / (a * Y)) := add_le_add
          (mul_le_mul_of_nonneg_left (h1 _) hYinv)
          (mul_le_mul (h0 _) hinv (by positivity) hM)
        _ = C := by unfold C; field_simp
  have hBY : 0 ≤ B * Y := mul_nonneg hB hY.le
  have hfin : volume (Set.Ioc 0 (B * Y)) < ⊤ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  calc
    _ ≤ ∫ _ in Set.Ioc 0 (B * Y), C :=
      setIntegral_mono_on (hFY.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
        (integrableOn_const hfin.ne) measurableSet_Ioc hbound
    _ = _ := by
      rw [setIntegral_const, Real.volume_real_Ioc_of_le hBY, sub_zero, smul_eq_mul]
      unfold C
      field_simp

end
end ArtinMatthews
