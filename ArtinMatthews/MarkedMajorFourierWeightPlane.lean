module

public import ArtinMatthews.MarkedMajorFourierWeight
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set
noncomputable section

def markedMajorFourierPlaneWeight (W : ℝ) (n : ℕ) (p : ℝ × ℝ) : ℝ :=
  markedMajorFourierWeight W n p.1 * markedMajorFourierWeight W n p.2

theorem markedMajorFourierPlaneWeight_nonneg {W : ℝ} (hW : 0 < W) (n : ℕ) (p : ℝ × ℝ) :
    0 ≤ markedMajorFourierPlaneWeight W n p :=
  mul_nonneg (markedMajorFourierWeight_nonneg hW n _) (markedMajorFourierWeight_nonneg hW n _)

theorem markedMajorFourierPlaneWeight_integrable {W : ℝ} (hW : 0 < W) {n : ℕ} (hn : 2 ≤ n) :
    Integrable (markedMajorFourierPlaneWeight W n) :=
  (markedMajorFourierWeight_integrable hW hn).mul_prod (markedMajorFourierWeight_integrable hW hn)

theorem markedMajorFourierPlaneWeight_integral_two {W : ℝ} (hW : 0 < W) :
    (∫ p : ℝ × ℝ, markedMajorFourierPlaneWeight W 2 p) = (W*markedMajorFourierWeightMass)^2 := by
  change (∫ p : ℝ × ℝ, markedMajorFourierWeight W 2 p.1 * markedMajorFourierWeight W 2 p.2) = _
  rw [Measure.volume_eq_prod,integral_prod_mul]
  rw [markedMajorFourierWeight_integral_two hW]
  ring

theorem markedMajorFourierPlaneWeight_tail_pointwise {W R : ℝ} (hW : 0 < W) (hR : 0 ≤ R)
    (n : ℕ) {p : ℝ × ℝ} (hp : R ≤ |p.1| ∨ R ≤ |p.2|) :
    markedMajorFourierPlaneWeight W (n+2) p ≤
      ((1+R/W)^n)⁻¹ * markedMajorFourierPlaneWeight W 2 p := by
  have hD : 0 ≤ ((1+R/W)^n)⁻¹ := by positivity
  unfold markedMajorFourierPlaneWeight
  rcases hp with hp | hp
  · calc
      _ ≤ (((1+R/W)^n)⁻¹ * markedMajorFourierWeight W 2 p.1) *
          markedMajorFourierWeight W 2 p.2 :=
        mul_le_mul (markedMajorFourierWeight_tail_pointwise hW hR n hp)
          (markedMajorFourierWeight_le_two hW (by omega) p.2)
          (markedMajorFourierWeight_nonneg hW _ _)
          (mul_nonneg hD (markedMajorFourierWeight_nonneg hW _ _))
      _ = _ := by ring
  · calc
      _ ≤ markedMajorFourierWeight W 2 p.1 *
          (((1+R/W)^n)⁻¹ * markedMajorFourierWeight W 2 p.2) :=
        mul_le_mul (markedMajorFourierWeight_le_two hW (by omega) p.1)
          (markedMajorFourierWeight_tail_pointwise hW hR n hp)
          (markedMajorFourierWeight_nonneg hW _ _) (markedMajorFourierWeight_nonneg hW _ _)
      _ = _ := by ring

theorem markedMajorFourier_coefficient_L1_bound (F : SchwartzMap (ℝ × ℝ) ℂ)
    {W C : ℝ} (hW : 0 < W)
    (hF : ∀ p, ‖F p‖ ≤ C*markedMajorFourierPlaneWeight W 2 p) :
    (∫ p : ℝ × ℝ, ‖F p‖) ≤ C*(W*markedMajorFourierWeightMass)^2 := by
  have hg := (markedMajorFourierPlaneWeight_integrable hW (by omega : 2 ≤ 2)).const_mul C
  have hi : Integrable (fun p => ‖F p‖) := hg.mono' F.continuous.norm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => by simpa only [norm_norm] using hF p))
  calc
    _ ≤ ∫ p : ℝ × ℝ, C*markedMajorFourierPlaneWeight W 2 p :=
      integral_mono hi hg hF
    _ = _ := by rw [integral_const_mul,markedMajorFourierPlaneWeight_integral_two hW]

theorem markedMajorFourier_coefficient_tail_bound (F : SchwartzMap (ℝ × ℝ) ℂ)
    {W R C : ℝ} (hW : 0 < W) (hR : 0 ≤ R) (hC : 0 ≤ C) (n : ℕ)
    (hF : ∀ p, ‖F p‖ ≤ C*markedMajorFourierPlaneWeight W (n+2) p) :
    (∫ p : ℝ × ℝ in {p | R ≤ |p.1| ∨ R ≤ |p.2|}, ‖F p‖) ≤
      C*((1+R/W)^n)⁻¹*(W*markedMajorFourierWeightMass)^2 := by
  let S : Set (ℝ × ℝ) := {p | R ≤ |p.1| ∨ R ≤ |p.2|}
  have hS : MeasurableSet S :=
    (measurableSet_le measurable_const (continuous_abs.comp continuous_fst).measurable).union
      (measurableSet_le measurable_const (continuous_abs.comp continuous_snd).measurable)
  have hg := (markedMajorFourierPlaneWeight_integrable hW (by omega : 2 ≤ 2)).const_mul
    (C*((1+R/W)^n)⁻¹)
  have hi : Integrable (fun p => ‖F p‖) :=
    ((markedMajorFourierPlaneWeight_integrable hW (by omega : 2 ≤ n+2)).const_mul C).mono'
      F.continuous.norm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => by simpa only [norm_norm] using hF p))
  calc
    _ ≤ ∫ p in S, (C*((1+R/W)^n)⁻¹)*markedMajorFourierPlaneWeight W 2 p :=
      setIntegral_mono_on hi.integrableOn hg.integrableOn hS (fun p hp => by
        calc
          ‖F p‖ ≤ C*markedMajorFourierPlaneWeight W (n+2) p := hF p
          _ ≤ C*(((1+R/W)^n)⁻¹*markedMajorFourierPlaneWeight W 2 p) :=
            mul_le_mul_of_nonneg_left (markedMajorFourierPlaneWeight_tail_pointwise hW hR n hp) hC
          _ = _ := by ring)
    _ ≤ ∫ p, (C*((1+R/W)^n)⁻¹)*markedMajorFourierPlaneWeight W 2 p :=
      setIntegral_le_integral hg (Filter.Eventually.of_forall (fun p =>
        mul_nonneg (by positivity) (markedMajorFourierPlaneWeight_nonneg hW 2 p)))
    _ = _ := by rw [integral_const_mul,markedMajorFourierPlaneWeight_integral_two hW]

end
end ArtinMatthews
