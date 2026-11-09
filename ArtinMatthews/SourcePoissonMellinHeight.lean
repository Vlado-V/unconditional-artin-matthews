module

public import ArtinMatthews.SourceLogRadialShear
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Prod


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open MeasureTheory
noncomputable section

/-- The three real heights, in the order of the two retained coordinates
`w,z` and the outer coordinate `ξ`. -/
abbrev SourcePoissonHeights := (ℝ × ℝ) × ℝ

def sourcePoissonHeightMeasure : Measure SourcePoissonHeights :=
  ((volume : Measure ℝ).prod volume).prod volume

def sourcePoissonVertical (σ t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I

@[simp] theorem sourcePoissonVertical_re (σ t : ℝ) :
    (sourcePoissonVertical σ t).re = σ := by
  simp [sourcePoissonVertical, Complex.mul_re]

@[simp] theorem sourcePoissonVertical_im (σ t : ℝ) :
    (sourcePoissonVertical σ t).im = t := by
  simp [sourcePoissonVertical, Complex.mul_im]

theorem sourcePoissonVertical_continuous (σ : ℝ) : Continuous (sourcePoissonVertical σ) := by
  unfold sourcePoissonVertical
  fun_prop

/-- The Gaussian decays in the sum of the outer and inner heights. -/
theorem sourcePoissonGaussian_norm (a c u t : ℝ) :
    ‖Complex.exp ((sourcePoissonVertical a u + sourcePoissonVertical c t - 1) ^ 2)‖ =
      Real.exp ((a + c - 1) ^ 2) * Real.exp (-((u + t) ^ 2)) := by
  rw [Complex.norm_exp, ← Real.exp_add]
  congr 1
  simp only [pow_two, Complex.mul_re, Complex.sub_re, Complex.add_re, Complex.one_re,
    sourcePoissonVertical_re, Complex.sub_im, Complex.add_im, Complex.one_im,
    sourcePoissonVertical_im, sub_zero]
  ring

/-- Absolute convergence of the product majorant after the exact height shear. -/
theorem sourcePoissonHeightMajorant_integrable (W M : ℝ → ℂ)
    (hW : Integrable W) (hM : Integrable M) :
    Integrable (fun p : SourcePoissonHeights =>
      (‖W p.1.1‖ * ‖M p.1.2‖) * Real.exp (-((p.2 + p.1.2) ^ 2)))
      sourcePoissonHeightMeasure := by
  have hG : Integrable (fun r : ℝ => Real.exp (-(r ^ 2))) := by
    simpa using integrable_exp_neg_mul_sq (b := 1) (by norm_num)
  have hp := (hW.norm.mul_prod hM.norm).mul_prod hG
  have hs := sourceLogRadial_shear_measurePreserving ((volume : Measure ℝ).prod volume)
    (Prod.snd : ℝ × ℝ → ℝ) measurable_snd
  exact hs.integrable_comp_of_integrable hp

end
end ArtinMatthews.SourcePhysical
