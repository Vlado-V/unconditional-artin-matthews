module

public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set
noncomputable section

def markedMajorFourierWeight (W : ℝ) (n : ℕ) (t : ℝ) : ℝ := ((1+|t|/W)^n)⁻¹

theorem markedMajorFourierWeight_nonneg {W : ℝ} (hW : 0 < W) (n : ℕ) (t : ℝ) :
    0 ≤ markedMajorFourierWeight W n t := by unfold markedMajorFourierWeight; positivity

theorem markedMajorFourierWeight_integrable_base : Integrable (markedMajorFourierWeight 1 2) := by
  have h : Integrable (fun t : ℝ => (1+‖t‖)^(-(2 : ℝ))) :=
    integrable_one_add_norm (by norm_num)
  have he (t : ℝ) : (1+‖t‖)^(-(2 : ℝ)) = markedMajorFourierWeight 1 2 t := by
    rw [Real.rpow_neg (by positivity),Real.rpow_two]
    simp only [markedMajorFourierWeight,div_one,Real.norm_eq_abs]
  simpa only [he] using h

theorem markedMajorFourierWeight_dilate {W : ℝ} (hW : 0 < W) (n : ℕ) (t : ℝ) :
    markedMajorFourierWeight W n t = markedMajorFourierWeight 1 n (t/W) := by
  simp only [markedMajorFourierWeight,abs_div,abs_of_pos hW,div_one]

theorem markedMajorFourierWeight_integrable_two {W : ℝ} (hW : 0 < W) :
    Integrable (markedMajorFourierWeight W 2) := by
  simpa only [← markedMajorFourierWeight_dilate hW] using
    (integrable_comp_div_iff (markedMajorFourierWeight 1 2) hW.ne').mpr
      markedMajorFourierWeight_integrable_base

def markedMajorFourierWeightMass : ℝ := ∫ t : ℝ, markedMajorFourierWeight 1 2 t

theorem markedMajorFourierWeightMass_nonneg : 0 ≤ markedMajorFourierWeightMass :=
  integral_nonneg (markedMajorFourierWeight_nonneg (by norm_num) 2)

theorem markedMajorFourierWeight_integral_two {W : ℝ} (hW : 0 < W) :
    (∫ t : ℝ, markedMajorFourierWeight W 2 t) = W*markedMajorFourierWeightMass := by
  simp_rw [markedMajorFourierWeight_dilate hW]
  rw [Measure.integral_comp_div,abs_of_pos hW,smul_eq_mul]
  rfl

theorem markedMajorFourierWeight_le_two {W : ℝ} (hW : 0 < W) {n : ℕ} (hn : 2 ≤ n) (t : ℝ) :
    markedMajorFourierWeight W n t ≤ markedMajorFourierWeight W 2 t := by
  unfold markedMajorFourierWeight
  have hb : 1 ≤ 1+|t|/W := le_add_of_nonneg_right (div_nonneg (abs_nonneg t) hW.le)
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hb hn)

theorem markedMajorFourierWeight_integrable {W : ℝ} (hW : 0 < W) {n : ℕ} (hn : 2 ≤ n) :
    Integrable (markedMajorFourierWeight W n) := by
  apply (markedMajorFourierWeight_integrable_two hW).mono'
  · apply Continuous.aestronglyMeasurable
    unfold markedMajorFourierWeight
    exact ((continuous_const.add (continuous_abs.div_const W)).pow n).inv₀
      (fun t => pow_ne_zero n (ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one
        (div_nonneg (abs_nonneg t) hW.le))))
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (markedMajorFourierWeight_nonneg hW n t)]
      exact markedMajorFourierWeight_le_two hW hn t)

theorem markedMajorFourierWeight_tail_pointwise {W R : ℝ} (hW : 0 < W) (hR : 0 ≤ R)
    (n : ℕ) {t : ℝ} (ht : R ≤ |t|) :
    markedMajorFourierWeight W (n+2) t ≤
      ((1+R/W)^n)⁻¹ * markedMajorFourierWeight W 2 t := by
  unfold markedMajorFourierWeight
  rw [pow_add,mul_inv]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity)
    (by gcongr) n)

theorem markedMajorFourierWeight_tail_integral {W R : ℝ} (hW : 0 < W) (hR : 0 ≤ R) (n : ℕ) :
    (∫ t : ℝ in {t | R ≤ |t|}, markedMajorFourierWeight W (n+2) t) ≤
      ((1+R/W)^n)⁻¹ * (W*markedMajorFourierWeightMass) := by
  let S : Set ℝ := {t | R ≤ |t|}
  have hS : MeasurableSet S := measurableSet_le measurable_const continuous_abs.measurable
  have hg := (markedMajorFourierWeight_integrable_two hW).const_mul ((1+R/W)^n)⁻¹
  calc
    _ ≤ ∫ t in S, ((1+R/W)^n)⁻¹ * markedMajorFourierWeight W 2 t :=
      setIntegral_mono_on (markedMajorFourierWeight_integrable hW (by omega)).integrableOn
        hg.integrableOn hS (fun _ ht => markedMajorFourierWeight_tail_pointwise hW hR n ht)
    _ ≤ ∫ t, ((1+R/W)^n)⁻¹ * markedMajorFourierWeight W 2 t :=
      setIntegral_le_integral hg (Filter.Eventually.of_forall (fun t =>
        mul_nonneg (by positivity) (markedMajorFourierWeight_nonneg hW 2 t)))
    _ = _ := by rw [integral_const_mul,markedMajorFourierWeight_integral_two hW]

end
end ArtinMatthews
