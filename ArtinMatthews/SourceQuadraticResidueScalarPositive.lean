module

public import ArtinMatthews.SourceQuadraticFullResidue
public import OAI.NumberTheory.DirichletL.Detector.RadialMellin


set_option backward.privateInPublic true
@[expose] public section

/-! Reality and positivity of the residue scalar for the actual nonnegative
compact source weight. -/

namespace ArtinMatthews.SourceEulerAssembly

open NumberField MeasureTheory Set
open scoped NumberField Classical BigOperators

noncomputable section

theorem sourceQuadraticB2Bump_mellin_half_ofReal :
    mellin (fun t : ℝ => (sourceQuadraticB2Bump t : ℂ)) (1 / 2) =
      ((∫ t : ℝ in Ioi 0, t ^ ((1 / 2 : ℝ) - 1) * sourceQuadraticB2Bump t : ℝ) : ℂ) := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    OAI.SevenEighths.ProbeRadialMellin.mellin_real, ← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only [Complex.real_smul, Complex.ofReal_mul]

theorem sourceQuadraticB2Bump_half_integral_nonneg :
    0 ≤ ∫ t : ℝ in Ioi 0, t ^ ((1 / 2 : ℝ) - 1) * sourceQuadraticB2Bump t := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_nonneg (Real.rpow_nonneg ht.le _) (sourceQuadraticB2Bump_nonneg t)

variable (F : Type) [Field F] [NumberField F]

theorem sourceQuadraticSmallResidueFactor_ofReal (M : ℝ) :
    sourceQuadraticSmallResidueFactor F M =
      ((dedekindZeta_residue F * Real.sqrt M * ((1 / 2 : ℝ) *
        ∫ t : ℝ in Ioi 0, t ^ ((1 / 2 : ℝ) - 1) * sourceQuadraticB2Bump t) : ℝ) : ℂ) := by
  rw [sourceQuadraticSmallResidueFactor, sourceQuadraticB2Bump_mellin_half_ofReal]
  push_cast
  rfl

theorem sourceQuadraticSmallResidueFactor_nonnegative (M : ℝ) :
    0 ≤ (sourceQuadraticSmallResidueFactor F M).re ∧
      (sourceQuadraticSmallResidueFactor F M).im = 0 := by
  rw [sourceQuadraticSmallResidueFactor_ofReal]
  simp only [Complex.ofReal_re, Complex.ofReal_im, and_true]
  exact mul_nonneg
    (mul_nonneg (dedekindZeta_residue_pos F).le (Real.sqrt_nonneg M))
    (mul_nonneg (by norm_num) sourceQuadraticB2Bump_half_integral_nonneg)

end
end ArtinMatthews.SourceEulerAssembly
