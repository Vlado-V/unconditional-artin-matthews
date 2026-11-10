module

public import ArtinMatthews.SpectralJGaussianTail
public import ArtinMatthews.SpectralKLIntegrableAnalysis
public import ArtinMatthews.SpectralKLUnitary
public import ArtinMatthews.SpectralDampedKMellin
public import ArtinMatthews.SpectralKLIntegrableCalibration
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set Filter
open OAI.CubicEisenstein
noncomputable section

theorem spectralJGaussianTail_nonpositive (F : ℝ → ℂ) (Y : ℝ) (hY : Y ≤ 0) :
    spectralJGaussianTail F Y = 0 := by
  simp only [spectralJGaussianTail, if_neg (not_lt.mpr hY)]

theorem spectralJGaussian_damped_zero_norm (Y : ℝ) (hY : 0 < Y) :
    ‖(Y : ℂ) ^ ((1 / 2 : ℂ) - 1) * Complex.exp (-(Y : ℂ)) *
      schlafliBesselK 0 Y‖ =
      Real.exp (-Y) / Real.sqrt Y * spectralKLRealKernel 0 Y := by
  have hK : schlafliBesselK 0 Y = (spectralKLRealKernel 0 Y : ℂ) := by
    simpa only [Complex.ofReal_zero, zero_mul] using
      schlafliBesselK_imaginary_eq_realKernel 0 hY
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY,
    Complex.norm_exp, hK, Complex.norm_real,
    Real.norm_of_nonneg spectralKLRealKernel_zero_nonneg]
  have he : ((1 / 2 : ℂ) - 1).re = -(1 / 2 : ℝ) := by norm_num
  rw [he, Complex.neg_re, Complex.ofReal_re]
  have hp : Y ^ (-(1 / 2 : ℝ)) = (Real.sqrt Y)⁻¹ := by
    rw [Real.rpow_neg hY.le, Real.sqrt_eq_rpow]
  rw [hp]
  ring

theorem spectralJGaussianTail_majorant_integrable (F : ℝ → ℂ)
    (hFm : Measurable F) (hF : IntegrableOn F (Ioi (2 : ℝ))) :
    Integrable (spectralKLIntegrableMajorant (spectralJGaussianTail F)) := by
  let D : ℝ := ∫ w in Ioi (2 : ℝ), ‖F w‖
  have hD : 0 ≤ D := integral_nonneg fun _ => norm_nonneg _
  have hzero := (spectralDampedK_mellin_integrable (0 : ℂ) (1 / 2 : ℂ)
    (by norm_num)).norm
  have hm : Measurable (spectralKLIntegrableMajorant (spectralJGaussianTail F)) := by
    unfold spectralKLIntegrableMajorant spectralKLPhysicalCompactDiv
    exact ((spectralKLRealKernel_stronglyMeasurable.measurable.comp
      (measurable_const.prodMk measurable_id)).mul
      (((spectralJGaussianTail_measurable F hFm).div
        Complex.continuous_ofReal.measurable).norm))
  have hbound : IntegrableOn (spectralKLIntegrableMajorant (spectralJGaussianTail F))
      (Ioi (0 : ℝ)) := by
    apply (hzero.const_mul D).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with Y hY
    change 0 < Y at hY
    rw [spectralJGaussian_damped_zero_norm Y hY]
    unfold spectralKLIntegrableMajorant spectralKLPhysicalCompactDiv
    rw [Real.norm_of_nonneg (mul_nonneg spectralKLRealKernel_zero_nonneg (norm_nonneg _)),
      norm_div, Complex.norm_real, Real.norm_of_nonneg hY.le]
    calc
      _ ≤ spectralKLRealKernel 0 Y *
          (Real.sqrt Y * Real.exp (-Y) * D / Y) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (spectralJGaussianTail_bound F hF Y hY) hY.le)
          spectralKLRealKernel_zero_nonneg
      _ = D * (Real.exp (-Y) / Real.sqrt Y * spectralKLRealKernel 0 Y) := by
        have hs : (Real.sqrt Y) ^ 2 = Y := Real.sq_sqrt hY.le
        have hs0 : Real.sqrt Y ≠ 0 := (Real.sqrt_pos.mpr hY).ne'
        have hr : Real.sqrt Y / Y = 1 / Real.sqrt Y := by
          apply (div_eq_div_iff hY.ne' hs0).mpr
          nlinarith
        calc
          _ = (Real.sqrt Y / Y) * (D * Real.exp (-Y) * spectralKLRealKernel 0 Y) := by ring
          _ = _ := by rw [hr]; ring
  have hi := (integrable_indicator_iff measurableSet_Ioi).mpr hbound
  apply hi.congr
  filter_upwards with Y
  by_cases hY : 0 < Y
  · exact indicator_of_mem hY _
  · rw [Set.indicator_of_notMem (show Y ∉ Ioi (0 : ℝ) from hY)]
    simp only [spectralKLIntegrableMajorant,
      spectralKLPhysicalCompactDiv, spectralJGaussianTail_nonpositive F Y (le_of_not_gt hY),
      zero_div, norm_zero, mul_zero]

theorem spectralJGaussianTail_completed_analysis (F : ℝ → ℂ)
    (hFm : Measurable F) (hF : IntegrableOn F (Ioi (2 : ℝ))) :
    spectralKLAnalysis ((spectralJGaussianTail_memLp F hFm hF).toLp
      (spectralJGaussianTail F)) =ᵐ[spectralKLSpectralMeasure]
      spectralKLPhysicalAnalysisIntegral (spectralJGaussianTail F) :=
  spectralKLAnalysis_majorant_ae _ (spectralJGaussianTail_measurable F hFm)
    (spectralJGaussianTail_nonpositive F)
    (spectralJGaussianTail_majorant_integrable F hFm hF)
    (spectralJGaussianTail_memLp F hFm hF)

end
end ArtinMatthews
