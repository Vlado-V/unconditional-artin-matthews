module

public import ArtinMatthews.SpectralCuspFourierODESection
public import ArtinMatthews.SpectralSectionLaplacian
public import ArtinMatthews.SpectralCuspFourierODEProjection
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The literal Fourier coefficients of a smooth periodic hyperbolic
Laplace eigenfunction satisfy the vertical Whittaker equation, including
the exact zero mode. Smoothness and the pointwise eigen-equation remain
explicit hypotheses for the independently constructed representatives. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace ArtinMatthews

theorem spectralSectionPlane_laplacian_equation (F : UpperHalfPlane → ℂ) (eigenvalue : ℝ)
    (hEq : ∀ z, h2SectionPositiveLaplacian F z = (eigenvalue : ℂ) * F z)
    (p : ℝ × ℝ) (hp : 0 < p.2) :
    -(p.2 ^ 2) • (spectralPlaneSecond (spectralSectionPlane F) 0 p +
      spectralPlaneSecond (spectralSectionPlane F) 1 p) = (eigenvalue : ℂ) * spectralSectionPlane F p := by
  rcases p with ⟨x, y⟩
  let z : UpperHalfPlane := ⟨(x : ℂ) + (y : ℂ) * Complex.I, by simpa using hp⟩
  have hx : z.re = x := by simp [z]
  have hy : z.im = y := by simp [z]
  have hf : spectralSectionPlane F (x, y) = F z := by
    simpa only [hx, hy] using spectralSectionPlane_at_upper F z
  have he := hEq z
  rw [h2SectionPositiveLaplacian, spectralPlanePositiveHyperbolic,
    spectralPlanePositiveSecond, Fin.sum_univ_two, hx, hy, ← hf] at he
  simpa only [smul_neg, neg_smul] using he

theorem cuspSectionFourierCoeff_whittakerODE (w : ℝ) (hw : 0 < w) (n : ℤ)
    (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun z : ℂ => F (UpperHalfPlane.ofComplex z))
      {z : ℂ | 0 < z.im})
    (hp : ∀ y > 0, Function.Periodic (fun x => spectralSectionPlane F (x, y)) w)
    (eigenvalue : ℝ) (hEq : ∀ z, h2SectionPositiveLaplacian F z = (eigenvalue : ℂ) * F z)
    {y : ℝ} (hy : 0 < y) :
    -(y ^ 2) • (deriv (deriv (cuspSectionFourierCoeff w n F)) y -
      ((cuspFourierFrequency w n : ℝ) : ℂ) ^ 2 * cuspSectionFourierCoeff w n F y) =
      (eigenvalue : ℂ) * cuspSectionFourierCoeff w n F y := by
  let Y := y / 2
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hYy : Y < y := by dsimp [Y]; linarith
  let G := spectralSectionSmoothExtension Y F
  have hG : ContDiff ℝ ∞ G := spectralSectionSmoothExtension_contDiff hY F hF
  have hg (x : ℝ) : G (x, y) = spectralSectionPlane F (x, y) :=
    spectralSectionSmoothExtension_eq hY F hYy.le
  have he (x : ℝ) : -(y ^ 2) • (spectralPlaneSecond G 0 (x, y) +
      spectralPlaneSecond G 1 (x, y)) = (eigenvalue : ℂ) * G (x, y) := by
    have hloc := spectralSectionSmoothExtension_germ hY F (p := (x, y)) hYy
    rw [spectralPlaneSecond_congr_of_eventuallyEq G (spectralSectionPlane F) hloc 0,
      spectralPlaneSecond_congr_of_eventuallyEq G (spectralSectionPlane F) hloc 1, hg]
    exact spectralSectionPlane_laplacian_equation F eigenvalue hEq (x, y) hy
  have hperiod : Function.Periodic (fun x => G (x, y)) w := by
    intro x
    dsimp only
    rw [hg, hg]
    exact hp y hy x
  have hvalue : cuspHorizontalWeightedMean w (cuspFourierPhase w n) G y =
      cuspSectionFourierCoeff w n F y :=
    cuspHorizontalWeightedMean_congr_slice w _ hg
  have hvertical : cuspHorizontalWeightedMean w (cuspFourierPhase w n)
      (spectralPlaneSecond G 1) y = cuspSectionFourierCoeffSecond w n F y := by
    apply cuspHorizontalWeightedMean_congr_slice
    intro x
    exact spectralPlaneSecond_congr_of_eventuallyEq G (spectralSectionPlane F)
      (spectralSectionSmoothExtension_germ hY F (p := (x, y)) hYy) 1
  have H := cuspFourierMean_laplacian_projection w hw n G hG y eigenvalue he
  rw [cuspFourierMean_second_horizontal w hw n G hG y hperiod, hvalue, hvertical,
    ← cuspSectionFourierCoeff_second_deriv w n F hF hy] at H
  simpa only [sub_eq_add_neg, add_comm] using H

theorem cuspSectionFourierCoeff_normalODE (w : ℝ) (hw : 0 < w) (n : ℤ)
    (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun z : ℂ => F (UpperHalfPlane.ofComplex z))
      {z : ℂ | 0 < z.im})
    (hp : ∀ y > 0, Function.Periodic (fun x => spectralSectionPlane F (x, y)) w)
    (eigenvalue : ℝ) (hEq : ∀ z, h2SectionPositiveLaplacian F z = (eigenvalue : ℂ) * F z)
    {y : ℝ} (hy : 0 < y) :
    deriv (deriv (cuspSectionFourierCoeff w n F)) y =
      (((cuspFourierFrequency w n : ℝ) : ℂ) ^ 2 - (eigenvalue : ℂ) / (y : ℂ) ^ 2) *
        cuspSectionFourierCoeff w n F y := by
  have H := cuspSectionFourierCoeff_whittakerODE w hw n F hF hp eigenvalue hEq hy
  simp only [Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_pow] at H
  have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  field_simp [hyc]
  linear_combination -H

theorem cuspSectionFourierCoeff_zero_mode (w : ℝ) (F : UpperHalfPlane → ℂ) :
    cuspSectionFourierCoeff w 0 F = cuspHorizontalMean w (spectralSectionPlane F) := by
  unfold cuspSectionFourierCoeff cuspHorizontalWeightedMean cuspFourierPhase cuspFourierFrequency
  simp only [Int.cast_zero, mul_zero, zero_div, Complex.ofReal_zero, neg_zero,
    zero_mul, Complex.exp_zero, one_mul]

theorem cuspSectionFourierCoeff_zeroMode_ODE (w : ℝ) (hw : 0 < w)
    (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun z : ℂ => F (UpperHalfPlane.ofComplex z))
      {z : ℂ | 0 < z.im})
    (hp : ∀ y > 0, Function.Periodic (fun x => spectralSectionPlane F (x, y)) w)
    (eigenvalue : ℝ) (hEq : ∀ z, h2SectionPositiveLaplacian F z = (eigenvalue : ℂ) * F z)
    {y : ℝ} (hy : 0 < y) :
    -(y ^ 2) • deriv (deriv (cuspHorizontalMean w (spectralSectionPlane F))) y =
      (eigenvalue : ℂ) * cuspHorizontalMean w (spectralSectionPlane F) y := by
  have H := cuspSectionFourierCoeff_whittakerODE w hw 0 F hF hp eigenvalue hEq hy
  simpa only [cuspSectionFourierCoeff_zero_mode, cuspFourierFrequency, Int.cast_zero,
    mul_zero, zero_div, Complex.ofReal_zero, zero_pow (by norm_num : 2 ≠ 0),
    zero_mul, sub_zero] using H

end ArtinMatthews
