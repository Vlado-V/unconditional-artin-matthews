module

public import ArtinMatthews.SpectralKLInverseIEnvelope
public import ArtinMatthews.SpectralHalfStripIdentity
public import ArtinMatthews.SpectralKLPointwiseCalibration
public import ArtinMatthews.SpectralKLPowerOrder
public import ArtinMatthews.SpectralKLWindowSmallBound
public import ArtinMatthews.SpectralKLWindowSynthesisBounds
public import ArtinMatthews.SpectralKLWindowSynthesisL2
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
open scoped ContDiff
noncomputable section

theorem spectralKLWindowData_even (h : ℂ → ℂ) (g : ℝ → ℂ)
    (hp : tsupport g ⊆ Ioi (0 : ℝ)) (hh : ∀ z : ℂ, h (-z) = h z) (t : ℝ) :
    spectralKLWindowData h g (-t) = spectralKLWindowData h g t := by
  unfold spectralKLWindowData
  rw [Complex.ofReal_neg, neg_mul, hh, spectralKLCompactOrderTransform_even g hp]

theorem spectralKLPowerOrderTransform_eq_integral (f : ℝ → ℂ)
    (hfzero : ∀ x : ℝ, x ≤ 0 → f x = 0) (ν : ℂ) :
    spectralKLCompactOrderTransform f ν =
      ∫ x in Ioi (0 : ℝ), schlafliBesselK ν x * f x / (x : ℂ) := by
  unfold spectralKLCompactOrderTransform
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ)) (fun x hx => ?_)]
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    unfold spectralKLCompactOrderIntegrand spectralKLPhysicalCompactDiv
    ring
  · simp [spectralKLCompactOrderIntegrand, spectralKLPhysicalCompactDiv, hfzero x (le_of_not_gt hx)]

theorem spectralKLPowerOrderTransform_imaginary (f : ℝ → ℂ)
    (hfzero : ∀ x : ℝ, x ≤ 0 → f x = 0) (t : ℝ) :
    spectralKLCompactOrderTransform f ((t : ℂ) * I) = spectralKLPhysicalAnalysisIntegral f t := by
  unfold spectralKLCompactOrderTransform spectralKLPhysicalAnalysisIntegral
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : 0 < x
  · simp only [spectralKLCompactOrderIntegrand, schlafliBesselK_imaginary_eq_realKernel t hx]
  · simp [spectralKLCompactOrderIntegrand, spectralKLPhysicalCompactDiv, hfzero x (le_of_not_gt hx)]

theorem spectralKLWindowSynthesis_analysis_pointwise (h : ℂ → ℂ) (g : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ))
    (heven : ∀ z : ℂ, h (-z) = h z)
    (hsmooth : ContDiff ℝ ∞ (fun t : ℝ => h (t : ℂ)))
    (hhol : ∀ z : ℂ, |z.im| ≤ 3 / 4 → DifferentiableAt ℂ h z)
    (C₀ : ℝ) (hbounded : ∀ t : ℝ, ‖h (t : ℂ)‖ ≤ C₀)
    (H : ℝ) (hH : 0 ≤ H)
    (hstrip : ∀ t y : ℝ, 0 ≤ y → y ≤ 3 / 4 →
      ‖h ((t : ℂ) + (y : ℂ) * I)‖ ≤ H * (1 + t ^ 2)) :
    ∀ t : ℝ, spectralKLPhysicalAnalysisIntegral (spectralKLWindowSynthesis h g) t =
      spectralKLWindowData h g t := by
  have hh (z : ℂ) (hz0 : 0 ≤ z.im) (hzB : z.im ≤ 3 / 4) :=
    hhol z (by rw [abs_of_nonneg hz0]; exact hzB)
  obtain ⟨M, hM, hpower⟩ := spectralKLWindowSynthesis_global_power_bound h g hg hc hp heven hh H hH hstrip
  have hR (t : ℝ) : ‖h (t : ℂ)‖ ≤ H * (1 + t ^ 2) := by
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using hstrip t 0 le_rfl (by norm_num)
  have hfm := spectralKLWindowSynthesis_measurable h g hsmooth.continuous hg hc hp H hH hR
  have hfLp := spectralKLWindowSynthesis_memLp h g hsmooth C₀ hbounded hg hc hp
  have hF := spectralKLWindowData_memLp h g hsmooth.continuous C₀ hbounded hg.continuous hc hp
  have hInv := spectralKLWindowSynthesis_inverse_ae h g hsmooth C₀ hbounded hg hc hp
  have hEq : hfLp.toLp (spectralKLWindowSynthesis h g) =
      spectralKLCompletedSynthesis (hF.toLp (spectralKLWindowData h g)) := by
    apply Lp.ext
    exact hfLp.coeFn_toLp.trans hInv.symm
  have hAnalysis : spectralKLAnalysis (hfLp.toLp (spectralKLWindowSynthesis h g)) =ᵐ[spectralKLSpectralMeasure]
      spectralKLWindowData h g := by
    rw [hEq, spectralKLAnalysis_synthesis]
    exact hF.coeFn_toLp
  apply spectralKLPower_analysis_eq (spectralKLWindowSynthesis h g) (spectralKLWindowData h g) hfm
    (fun x hx => by simp only [spectralKLWindowSynthesis, ite_eq_right (not_lt.mpr hx)]) hfLp
    M (3 / 4) hM (by norm_num) hpower
    (spectralKLWindowData_continuous h g hsmooth.continuous hg.continuous hc hp)
    (spectralKLWindowData_even h g hp heven) hAnalysis

theorem spectralKLWindowSynthesis_continued_transform (h : ℂ → ℂ) (g : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ))
    (heven : ∀ z : ℂ, h (-z) = h z)
    (hsmooth : ContDiff ℝ ∞ (fun t : ℝ => h (t : ℂ)))
    (hhol : ∀ z : ℂ, |z.im| ≤ 3 / 4 → DifferentiableAt ℂ h z)
    (C₀ : ℝ) (hbounded : ∀ t : ℝ, ‖h (t : ℂ)‖ ≤ C₀)
    (H : ℝ) (hH : 0 ≤ H)
    (hstrip : ∀ t y : ℝ, 0 ≤ y → y ≤ 3 / 4 →
      ‖h ((t : ℂ) + (y : ℂ) * I)‖ ≤ H * (1 + t ^ 2))
    (ν : ℂ) (hν : |ν.re| ≤ 1 / 2) :
    spectralKLCompactOrderTransform (spectralKLWindowSynthesis h g) ν =
      h (-I * ν) * spectralKLCompactOrderTransform g ν := by
  have hh (z : ℂ) (hz0 : 0 ≤ z.im) (hzB : z.im ≤ 3 / 4) :=
    hhol z (by rw [abs_of_nonneg hz0]; exact hzB)
  obtain ⟨M, hM, hpower⟩ := spectralKLWindowSynthesis_global_power_bound h g hg hc hp heven hh H hH hstrip
  have hR (t : ℝ) : ‖h (t : ℂ)‖ ≤ H * (1 + t ^ 2) := by
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using hstrip t 0 le_rfl (by norm_num)
  have hfm := spectralKLWindowSynthesis_measurable h g hsmooth.continuous hg hc hp H hH hR
  have hfzero : ∀ x : ℝ, x ≤ 0 → spectralKLWindowSynthesis h g x = 0 :=
    fun x hx => by simp only [spectralKLWindowSynthesis, ite_eq_right (not_lt.mpr hx)]
  apply spectral_half_strip_identity
    (spectralKLCompactOrderTransform (spectralKLWindowSynthesis h g))
    (fun μ => h (-I * μ) * spectralKLCompactOrderTransform g μ) ?_ ?_ ?_ ν hν
  · intro μ hμ
    exact (spectralKLPowerOrderTransform_hasDerivAt _ hfm hfzero M hM hpower μ hμ).differentiableAt
  · intro μ hμ
    have hs : |(-I * μ).im| ≤ 3 / 4 := by
      simp only [neg_mul, Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add, abs_neg]
      exact hμ.trans (by norm_num)
    exact ((hhol _ hs).comp μ ((hasDerivAt_id μ).const_mul (-I)).differentiableAt).mul
      (spectralKLCompactOrderTransform_entire g hg.continuous hc hp μ)
  · intro t
    rw [spectralKLPowerOrderTransform_imaginary _ hfzero,
      spectralKLWindowSynthesis_analysis_pointwise h g hg hc hp heven hsmooth hhol C₀ hbounded H hH hstrip]
    have ht : -I * ((t : ℂ) * I) = (t : ℂ) := by linear_combination -(t : ℂ) * I_sq
    rw [ht]
    rfl

end
end ArtinMatthews
