module

public import ArtinMatthews.MarkedMajorMellinLocalMeanUnit
public import Mathlib.MeasureTheory.Group.Integral


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform weighted L² means at every positive scale and every shift.
The change of variables cancels the scale exactly. -/

noncomputable section
namespace ArtinMatthews
open MeasureTheory Set

theorem markedMajorLocalMean_integrable (Q : ℝ → ℂ) (hQ : Continuous Q)
    (B : ℝ) (hB : ∀ t, ‖Q t‖ ≤ B) {X : ℝ} (hX : 0 < X) (c : ℝ) :
    Integrable (fun t : ℝ => markedMajorFourierWeight X 2 (t-c)*‖Q t‖^2) := by
  have hB0 : 0 ≤ B := (norm_nonneg (Q 0)).trans (hB 0)
  apply (((markedMajorFourierWeight_integrable_two hX).comp_sub_right c).mul_const (B^2)).mono'
  · exact (((markedMajorFourierWeight_continuous hX 2).comp (continuous_id.sub continuous_const)).mul
      (hQ.norm.pow 2)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (markedMajorFourierWeight_nonneg hX 2 (t-c)) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_left (by nlinarith [hB t, norm_nonneg (Q t)])
        (markedMajorFourierWeight_nonneg hX 2 (t-c)))

theorem markedMajorLocalMean_scaled_interval (Q : ℝ → ℂ)
    {X M : ℝ} (hX : 0 < X)
    (hlocal : ∀ a : ℝ, (∫ t in Icc a (a+X), ‖Q t‖^2) ≤ M) (c a : ℝ) :
    (∫ t in Icc a (a+1), ‖Q (X*t+c)‖^2) ≤ M/X := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : a ≤ a+1)]
  rw [intervalIntegral.integral_comp_mul_add (fun t => ‖Q t‖^2) hX.ne' c, smul_eq_mul]
  have hend : X*(a+1)+c = (X*a+c)+X := by ring
  rw [hend, intervalIntegral.integral_of_le (by linarith : X*a+c ≤ X*a+c+X),
    ← integral_Icc_eq_integral_Ioc]
  calc
    _ ≤ X⁻¹*M := mul_le_mul_of_nonneg_left (hlocal _) (inv_nonneg.mpr hX.le)
    _ = _ := by ring

theorem markedMajorLocalMean_scaled_integral (Q : ℝ → ℂ) {X : ℝ} (hX : 0 < X) (c : ℝ) :
    (∫ u : ℝ, markedMajorFourierWeight 1 2 u*‖Q (X*u+c)‖^2) =
      X⁻¹*(∫ t : ℝ, markedMajorFourierWeight X 2 (t-c)*‖Q t‖^2) := by
  let g : ℝ → ℝ := fun t => markedMajorFourierWeight X 2 (t-c)*‖Q t‖^2
  have he (u : ℝ) : g (X*u+c) = markedMajorFourierWeight 1 2 u*‖Q (X*u+c)‖^2 := by
    dsimp [g]
    rw [markedMajorFourierWeight_dilate hX]
    have hc : (X*u+c-c)/X = u := by field_simp; ring
    rw [hc]
  calc
    _ = ∫ u : ℝ, g (X*u+c) := integral_congr_ae (Filter.Eventually.of_forall (fun u => (he u).symm))
    _ = |X⁻¹| *(∫ t : ℝ, g (t+c)) := by
      exact Measure.integral_comp_mul_left (fun t => g (t+c)) X
    _ = X⁻¹*(∫ t : ℝ, g t) := by
      rw [integral_add_right_eq_self, abs_of_pos (inv_pos.mpr hX)]

theorem markedMajorLocalMean_weighted (Q : ℝ → ℂ) (hQ : Continuous Q)
    (B : ℝ) (hB : ∀ t, ‖Q t‖ ≤ B) {X M : ℝ} (hX : 0 < X) (hM : 0 ≤ M)
    (hlocal : ∀ a : ℝ, (∫ t in Icc a (a+X), ‖Q t‖^2) ≤ M) (c : ℝ) :
    (∫ t : ℝ, markedMajorFourierWeight X 2 (t-c)*‖Q t‖^2) ≤
      markedMajorLocalMeanConstant*M := by
  have hscaled := markedMajorLocalMean_unit (fun u => Q (X*u+c))
    (hQ.comp ((continuous_const.mul continuous_id).add_const c)) B (fun u => hB (X*u+c))
    (div_nonneg hM hX.le) (markedMajorLocalMean_scaled_interval Q hX hlocal c)
  rw [markedMajorLocalMean_scaled_integral Q hX c] at hscaled
  have h := mul_le_mul_of_nonneg_left hscaled hX.le
  have hleft : X*(X⁻¹*(∫ t : ℝ, markedMajorFourierWeight X 2 (t-c)*‖Q t‖^2)) =
      ∫ t : ℝ, markedMajorFourierWeight X 2 (t-c)*‖Q t‖^2 := by field_simp
  have hright : X*(markedMajorLocalMeanConstant*(M/X)) = markedMajorLocalMeanConstant*M := by field_simp
  rw [hleft, hright] at h
  exact h

end ArtinMatthews
