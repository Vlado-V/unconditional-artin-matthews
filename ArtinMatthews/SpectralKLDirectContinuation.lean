module

public import ArtinMatthews.SpectralKLCompactOrder
public import ArtinMatthews.SpectralKLDirectDefinitions
public import ArtinMatthews.SpectralHalfStripIdentity
public import ArtinMatthews.SpectralKLDirectL2
public import ArtinMatthews.SpectralKLDirectSmallBound
public import ArtinMatthews.SpectralKLPointwiseCalibration
public import ArtinMatthews.SpectralKLPowerOrder
public import ArtinMatthews.SpectralKLWindowContinuation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
open Set MeasureTheory Filter Complex OAI.CubicEisenstein
open scoped ContDiff ComplexConjugate
noncomputable section

theorem spectralKLDirectSynthesis_real (F : ℝ → ℂ)
    (hF : ∀ t : ℝ, star (F t) = F t) (x : ℝ) :
    star (spectralKLDirectSynthesis F x) = spectralKLDirectSynthesis F x := by
  have hreal (r : ℝ) : star (r : ℂ) = (r : ℂ) := by
    change conj (r : ℂ) = (r : ℂ)
    exact conj_ofReal r
  rw [spectralKLDirectSynthesis]
  by_cases hx : 0 < x
  · rw [ite_eq_left hx, spectralKLWeightedSynthesis]
    change conj _ = _
    rw [← integral_conj]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp only
    rw [schlafliBesselK_imaginary_eq_realKernel t hx]
    simpa only [map_mul, conj_ofReal, starRingEnd_apply, hreal] using congrArg
      (fun z : ℂ => (spectralKLRealKernel t x : ℂ) * z * (spectralKLPlancherelWeight t : ℂ)) (hF t)
  · simp only [ite_eq_right hx, star_zero]

theorem spectralKLDirectSynthesis_analysis_pointwise (F : ℂ → ℂ)
    (heven : ∀ z : ℂ, F (-z) = F z)
    (hsmooth : ContDiff ℝ ∞ (fun t : ℝ => F (t : ℂ)))
    (hhol : ∀ z : ℂ, |z.im| ≤ 3 / 4 → DifferentiableAt ℂ F z)
    (hrapid : SpectralKLDirectStripRapid F) :
    ∀ t : ℝ, spectralKLPhysicalAnalysisIntegral
      (spectralKLDirectSynthesis (fun t : ℝ => F (t : ℂ))) t = F (t : ℂ) := by
  let f : ℝ → ℂ := spectralKLDirectSynthesis (fun t : ℝ => F (t : ℂ))
  have hh (z : ℂ) (hz0 : 0 ≤ z.im) (hzB : z.im ≤ 3 / 4) :=
    hhol z (by rw [abs_of_nonneg hz0]; exact hzB)
  have hR := spectralKLDirectStripRapid_real hrapid
  obtain ⟨M, hM, hpower⟩ := spectralKLDirectSynthesis_global_power_bound F heven hh hrapid
  have hfm : Measurable f := spectralKLDirectSynthesis_measurable _ hsmooth.continuous hR
  have hfLp : MemLp f 2 spectralKLPhysicalMeasure :=
    spectralKLDirectSynthesis_memLp _ hsmooth.contDiffOn hsmooth.continuous hR
  have hFLp := spectralKLDirectData_memLp _ hsmooth.continuous hR
  have hInv := spectralKLDirectSynthesis_inverse_ae _ hsmooth.contDiffOn hsmooth.continuous hR
  have hEq : hfLp.toLp f = spectralKLCompletedSynthesis (hFLp.toLp (fun t : ℝ => F (t : ℂ))) := by
    apply Lp.ext
    exact hfLp.coeFn_toLp.trans hInv.symm
  have hAnalysis : spectralKLAnalysis (hfLp.toLp f) =ᵐ[spectralKLSpectralMeasure]
      (fun t : ℝ => F (t : ℂ)) := by
    rw [hEq, spectralKLAnalysis_synthesis]
    exact hFLp.coeFn_toLp
  apply spectralKLPower_analysis_eq f (fun t : ℝ => F (t : ℂ)) hfm
    (fun x hx => by simp only [f, spectralKLDirectSynthesis, ite_eq_right (not_lt.mpr hx)]) hfLp
    M (3 / 4) hM (by norm_num) hpower hsmooth.continuous
    (fun t => by simpa only [Complex.ofReal_neg] using heven (t : ℂ)) hAnalysis

theorem spectralKLDirectSynthesis_continued_transform (F : ℂ → ℂ)
    (heven : ∀ z : ℂ, F (-z) = F z)
    (hsmooth : ContDiff ℝ ∞ (fun t : ℝ => F (t : ℂ)))
    (hhol : ∀ z : ℂ, |z.im| ≤ 3 / 4 → DifferentiableAt ℂ F z)
    (hrapid : SpectralKLDirectStripRapid F)
    (ν : ℂ) (hν : |ν.re| ≤ 1 / 2) :
    spectralKLCompactOrderTransform (spectralKLDirectSynthesis (fun t : ℝ => F (t : ℂ))) ν = F (-I * ν) := by
  let f : ℝ → ℂ := spectralKLDirectSynthesis (fun t : ℝ => F (t : ℂ))
  have hh (z : ℂ) (hz0 : 0 ≤ z.im) (hzB : z.im ≤ 3 / 4) :=
    hhol z (by rw [abs_of_nonneg hz0]; exact hzB)
  have hR := spectralKLDirectStripRapid_real hrapid
  obtain ⟨M, hM, hpower⟩ := spectralKLDirectSynthesis_global_power_bound F heven hh hrapid
  have hfm : Measurable f := spectralKLDirectSynthesis_measurable _ hsmooth.continuous hR
  have hfzero : ∀ x : ℝ, x ≤ 0 → f x = 0 :=
    fun x hx => by simp only [f, spectralKLDirectSynthesis, ite_eq_right (not_lt.mpr hx)]
  apply spectral_half_strip_identity (spectralKLCompactOrderTransform f) (fun μ => F (-I * μ)) ?_ ?_ ?_ ν hν
  · intro μ hμ
    exact (spectralKLPowerOrderTransform_hasDerivAt f hfm hfzero M hM hpower μ hμ).differentiableAt
  · intro μ hμ
    have hs : |(-I * μ).im| ≤ 3 / 4 := by
      simp only [neg_mul, Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        zero_mul, one_mul, zero_add, abs_neg]
      exact hμ.trans (by norm_num)
    exact (hhol _ hs).comp μ ((hasDerivAt_id μ).const_mul (-I)).differentiableAt
  · intro t
    rw [spectralKLPowerOrderTransform_imaginary _ hfzero]
    change spectralKLPhysicalAnalysisIntegral
      (spectralKLDirectSynthesis (fun t : ℝ => F (t : ℂ))) t = _
    rw [spectralKLDirectSynthesis_analysis_pointwise F heven hsmooth hhol hrapid]
    have ht : -I * ((t : ℂ) * I) = (t : ℂ) := by linear_combination -(t : ℂ) * I_sq
    rw [ht]

end
end ArtinMatthews
