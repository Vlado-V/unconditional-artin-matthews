module

public import ArtinMatthews.SourceArchSelfDualMeasure
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals


set_option backward.privateInPublic true
@[expose] public section

/-! Exact radial integration for the complex trace measure. -/
namespace ArtinMatthews.SourceArchJacquet

open MeasureTheory MeasureTheory.Measure Set
open ArtinMatthews.VaryingKummerAnalytic
noncomputable section

theorem sourceArchTraceIntegral_radial (f : ℝ → ℂ) :
    (∫ z : ℂ, f ‖z‖ ∂sourceComplexTraceMeasure) =
      (4 * Real.pi : ℝ) * ∫ r : ℝ in Ioi 0, (r : ℂ) * f r := by
  have hp : (∫ z : ℂ, f ‖z‖) =
      (2 * Real.pi : ℝ) * ∫ r : ℝ in Ioi 0, (r : ℂ) * f r := by
    calc
      _ = ∫ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, (p.1 : ℂ) * f |p.1| := by
        simpa only [polarCoord_target, Complex.norm_polarCoord_symm, Complex.real_smul] using
          (Complex.integral_comp_polarCoord_symm (fun z : ℂ => f ‖z‖)).symm
      _ = (∫ r : ℝ in Ioi 0, (r : ℂ) * f |r|) * ∫ _ : ℝ in Ioo (-Real.pi) Real.pi, (1 : ℂ) := by
        rw [← setIntegral_prod_mul, volume_eq_prod]
        simp only [mul_one]
      _ = _ := by
        have he : (∫ r : ℝ in Ioi 0, (r : ℂ) * f |r|) = ∫ r : ℝ in Ioi 0, (r : ℂ) * f r := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro r hr
          dsimp only
          rw [abs_of_pos hr]
        rw [he, integral_const, measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter,
          Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
        simp only [Complex.real_smul, mul_one]
        push_cast
        ring
  unfold sourceComplexTraceMeasure
  rw [integral_smul_measure, hp]
  norm_num
  ring

theorem sourceArchRadialIntegral_square (f : ℝ → ℂ) :
    (∫ r : ℝ in Ioi 0, (r : ℂ) * f (r ^ 2)) =
      (1 / 2 : ℂ) * ∫ t : ℝ in Ioi 0, f t := by
  have h := integral_comp_rpow_Ioi_of_pos (g := f) (by norm_num : (0 : ℝ) < 2)
  have he : (fun r : ℝ => ((2 : ℝ) * r ^ ((2 : ℝ) - 1)) • f (r ^ (2 : ℝ))) =
      (fun r : ℝ => (2 : ℂ) * ((r : ℂ) * f (r ^ 2))) := by
    funext r
    norm_num [smul_eq_mul]
    ring
  rw [he, integral_const_mul] at h
  calc
    _ = (1 / 2 : ℂ) * ((2 : ℂ) * ∫ r : ℝ in Ioi 0, (r : ℂ) * f (r ^ 2)) := by ring
    _ = _ := by rw [h]

theorem sourceArchIntegral_shift_one (f : ℝ → ℂ) :
    (∫ t : ℝ in Ioi 0, f (1 + t)) = ∫ t : ℝ in Ioi 1, f t := by
  have h := integral_add_left_eq_self (μ := (volume : Measure ℝ)) (fun t : ℝ => (Ioi 1).indicator f t) (1 : ℝ)
  have he : (fun t : ℝ => (Ioi 1).indicator f (1 + t)) =
      (Ioi 0).indicator (fun t => f (1 + t)) := by
    funext t
    by_cases ht : 0 < t
    · have ht' : 1 < 1 + t := by linarith
      simp [ht, ht']
    · have ht' : ¬ 1 < 1 + t := by linarith
      simp [ht, ht']
  rw [he, integral_indicator measurableSet_Ioi, integral_indicator measurableSet_Ioi] at h
  exact h

end
end ArtinMatthews.SourceArchJacquet
