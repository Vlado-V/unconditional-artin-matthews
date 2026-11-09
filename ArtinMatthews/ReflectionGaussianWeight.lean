module

public import OAI.NumberTheory.DirichletL.Detector.GaussianMellin


set_option backward.privateInPublic true
@[expose] public section

/-! The literal logarithmic Gaussian in source02a, with its exact inverse
Mellin normalization and the power majorant needed for the actual B_m sum.
Only the geometry-free Gaussian identity is reused from the pinned source. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory
open OAI.SevenEighths.ProbePhysical
noncomputable section

def reflectionGaussian (t : ℝ) : ℝ :=
  1 / (2 * Real.sqrt Real.pi) * Real.exp (-(Real.log t) ^ 2 / 4)

theorem reflectionGaussian_pos (t : ℝ) : 0 < reflectionGaussian t := by
  unfold reflectionGaussian
  positivity

theorem reflectionGaussian_eq_mellinProfile {t : ℝ} (ht : 0 < t) :
    (reflectionGaussian t : ℂ) = gaussianMellinProfile t := by
  have hroot : (Real.pi : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt Real.pi : ℂ) := by
    rw [Real.sqrt_eq_rpow]
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      (Complex.ofReal_cpow Real.pi_pos.le (1 / 2)).symm
  have hcoef : ((1 / (2 * Real.pi) : ℝ) : ℂ) * (Real.pi : ℂ) ^ (1 / 2 : ℂ) =
      ((1 / (2 * Real.sqrt Real.pi) : ℝ) : ℂ) := by
    rw [hroot, ← Complex.ofReal_mul]
    congr 1
    have hs := Real.sq_sqrt Real.pi_pos.le
    have hs0 : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
    field_simp
    nlinarith
  unfold gaussianMellinProfile reflectionGaussian
  rw [hcoef, ← Complex.ofReal_log ht.le]
  push_cast
  rfl

theorem reflectionGaussian_inverse_mellin {t : ℝ} (ht : 0 < t) (σ : ℝ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ v : ℝ, (t : ℂ) ^ (-((σ : ℂ) + v * Complex.I)) *
        Complex.exp (((σ : ℂ) + v * Complex.I) ^ 2)) = (reflectionGaussian t : ℂ) :=
  (gaussianMellin_inversion t ht σ).trans (reflectionGaussian_eq_mellinProfile ht).symm

theorem reflectionGaussian_power_bound {t : ℝ} (ht : 0 < t) (σ : ℝ) :
    reflectionGaussian t ≤
      (Real.exp (σ ^ 2) / (2 * Real.sqrt Real.pi)) * t ^ (-σ) := by
  unfold reflectionGaussian
  rw [Real.rpow_def_of_pos ht]
  have he : -(Real.log t) ^ 2 / 4 ≤ σ ^ 2 + Real.log t * (-σ) := by
    nlinarith [sq_nonneg (Real.log t / 2 - σ)]
  have hm := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he)
    (by positivity : 0 ≤ 1 / (2 * Real.sqrt Real.pi))
  rw [Real.exp_add] at hm
  convert hm using 1
  ring

theorem reflectionGaussian_ratio_bound {Q Z : ℝ} (hQ : 0 < Q) (hZ : 0 < Z) (σ : ℝ) :
    reflectionGaussian (Q / Z) ≤
      (Real.exp (σ ^ 2) / (2 * Real.sqrt Real.pi)) * Z ^ σ * Q ^ (-σ) := by
  have hpow : (Q / Z) ^ (-σ) = Z ^ σ * Q ^ (-σ) := by
    rw [Real.rpow_def_of_pos (div_pos hQ hZ), Real.log_div hQ.ne' hZ.ne',
      Real.rpow_def_of_pos hQ, Real.rpow_def_of_pos hZ, ← Real.exp_add]
    congr 1
    ring
  have h := reflectionGaussian_power_bound (div_pos hQ hZ) σ
  rw [hpow] at h
  simpa only [mul_assoc] using h

end
end ArtinMatthews.VaryingKummerAnalytic
