module

public import ArtinMatthews.SourcePoissonMellinHeight
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open MeasureTheory
noncomputable section

/-- The three-line integrand after the source substitution `t = ξ + z - 1`.
The input `A` is the finite sum of the original frequency rows on these lines. -/
def sourcePoissonTripleKernel (X Y Z a b c : ℝ) (W M : ℝ → ℂ)
    (A : SourcePoissonHeights → ℂ) (p : SourcePoissonHeights) : ℂ :=
  let ξ := sourcePoissonVertical a p.2
  let w := sourcePoissonVertical b p.1.1
  let z := sourcePoissonVertical c p.1.2
  (X : ℂ) ^ (1 / 2 - z) * (Z : ℂ) ^ (ξ + z - 1) * (Y : ℂ) ^ (w - 1) *
    Complex.exp ((ξ + z - 1) ^ 2) * M p.1.2 * W p.1.1 * A p

def sourcePoissonTripleScale (X Y Z a b c : ℝ) : ℝ :=
  X ^ (1 / 2 - c) * Z ^ (a + c - 1) * Y ^ (b - 1) * Real.exp ((a + c - 1) ^ 2)

theorem sourcePoissonTripleKernel_norm {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (a b c : ℝ) (W M : ℝ → ℂ) (A : SourcePoissonHeights → ℂ) (p : SourcePoissonHeights) :
    ‖sourcePoissonTripleKernel X Y Z a b c W M A p‖ =
      (sourcePoissonTripleScale X Y Z a b c * ‖A p‖) *
      ((‖W p.1.1‖ * ‖M p.1.2‖) * Real.exp (-((p.2 + p.1.2) ^ 2))) := by
  simp only [sourcePoissonTripleKernel, sourcePoissonTripleScale, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hX, Complex.norm_cpow_eq_rpow_re_of_pos hY,
    Complex.norm_cpow_eq_rpow_re_of_pos hZ, sourcePoissonGaussian_norm,
    Complex.sub_re, Complex.add_re, Complex.one_re, sourcePoissonVertical_re]
  have hh : (1 / 2 : ℂ).re = (1 / 2 : ℝ) := by norm_num [Complex.div_re]
  rw [hh]
  ring

theorem sourcePoissonTripleKernel_measurable {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (a b c : ℝ) (W M : ℝ → ℂ) (A : SourcePoissonHeights → ℂ)
    (hW : Measurable W) (hM : Measurable M) (hA : Measurable A) :
    Measurable (sourcePoissonTripleKernel X Y Z a b c W M A) := by
  have hcont : Continuous (fun p : SourcePoissonHeights =>
      (X : ℂ) ^ (1 / 2 - sourcePoissonVertical c p.1.2) *
      (Z : ℂ) ^ (sourcePoissonVertical a p.2 + sourcePoissonVertical c p.1.2 - 1) *
      (Y : ℂ) ^ (sourcePoissonVertical b p.1.1 - 1) *
      Complex.exp ((sourcePoissonVertical a p.2 + sourcePoissonVertical c p.1.2 - 1) ^ 2)) := by
    simp_rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hX.ne'),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hY.ne'),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hZ.ne')]
    unfold sourcePoissonVertical
    fun_prop
  exact ((hcont.measurable.mul (hM.comp (measurable_snd.comp measurable_fst))).mul
    (hW.comp (measurable_fst.comp measurable_fst))).mul hA

theorem sourcePoissonTripleKernel_integrable {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (a b c : ℝ) (W M : ℝ → ℂ) (A : SourcePoissonHeights → ℂ)
    (hW : Integrable W) (hM : Integrable M)
    (hWm : Measurable W) (hMm : Measurable M) (hAm : Measurable A)
    (B : ℝ) (hB : ∀ p, ‖A p‖ ≤ B) :
    Integrable (sourcePoissonTripleKernel X Y Z a b c W M A) sourcePoissonHeightMeasure := by
  have hscale : 0 ≤ sourcePoissonTripleScale X Y Z a b c := by
    unfold sourcePoissonTripleScale
    positivity
  apply ((sourcePoissonHeightMajorant_integrable W M hW hM).const_mul
    (sourcePoissonTripleScale X Y Z a b c * B)).mono'
    (sourcePoissonTripleKernel_measurable hX hY hZ a b c W M A hWm hMm hAm).aestronglyMeasurable
  filter_upwards with p
  rw [sourcePoissonTripleKernel_norm hX hY hZ]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hB p) hscale) (by positivity)

end
end ArtinMatthews.SourcePhysical
