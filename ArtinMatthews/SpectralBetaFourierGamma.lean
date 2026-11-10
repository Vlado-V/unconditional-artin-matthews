module

public import ArtinMatthews.SpectralBetaLogistic
public import Mathlib.Analysis.Fourier.FourierTransform
public import ArtinMatthews.SpectralBesselMellinInversion
public import ArtinMatthews.SpectralGammaVerticalIntegrable
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The Fourier transform of the actual beta log profile is its Gamma
quotient, with genuine L1 convergence on the full Fourier line. -/

noncomputable section
open Set MeasureTheory Filter
open scoped FourierTransform

namespace ArtinMatthews

theorem spectralBetaLogProfile_fourier (a b : ℂ) (ξ : ℝ) :
    𝓕 (spectralBetaLogProfile a b) ξ =
      Complex.betaIntegral (a-(2*Real.pi*ξ : ℝ)*Complex.I)
        (b+(2*Real.pi*ξ : ℝ)*Complex.I) := by
  let z : ℂ := -((2*Real.pi*ξ : ℝ) : ℂ)*Complex.I
  have he1 : a-(2*Real.pi*ξ : ℝ)*Complex.I = a+z := by dsimp [z]; ring
  have he2 : b+(2*Real.pi*ξ : ℝ)*Complex.I = b-z := by dsimp [z]; ring
  rw [he1,he2,← spectralBetaLogProfile_integral,Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [spectralBetaLogProfile_shift]
  simp only [smul_eq_mul]
  have he : (((-2*Real.pi*u*ξ : ℝ) : ℂ)*Complex.I) = z*(u : ℂ) := by
    dsimp [z]
    push_cast
    ring
  rw [he,mul_comm]

theorem spectralBetaLogProfile_fourier_gamma (a b : ℂ) (ha : 0 < a.re) (hb : 0 < b.re) (ξ : ℝ) :
    𝓕 (spectralBetaLogProfile a b) ξ =
      Complex.Gamma (a-(2*Real.pi*ξ : ℝ)*Complex.I) *
        Complex.Gamma (b+(2*Real.pi*ξ : ℝ)*Complex.I) / Complex.Gamma (a+b) := by
  rw [spectralBetaLogProfile_fourier,Complex.betaIntegral_eq_Gamma_mul_div _ _
    (by simpa using ha) (by simpa using hb)]
  congr 2
  ring

theorem spectral_Gamma_complex_line_integrable (z : ℂ) (hz : 0 < z.re) (d : ℝ) (hd : d ≠ 0) :
    Integrable (fun t : ℝ => Complex.Gamma (z+(d*t : ℝ)*Complex.I)) := by
  have h := spectral_Gamma_affine_vertical_integrable z.re z.im d hz hd
  convert h using 1
  ext t
  congr 1
  apply Complex.ext <;> simp
  ring

theorem spectral_Gamma_complex_line_continuous (z : ℂ) (hz : 0 < z.re) (d : ℝ) :
    Continuous (fun t : ℝ => Complex.Gamma (z+(d*t : ℝ)*Complex.I)) := by
  have h := (spectral_Gamma_vertical_continuous z.re hz).comp
    (show Continuous (fun t : ℝ => d*t+z.im) by fun_prop)
  convert h using 1
  ext t
  congr 1
  apply Complex.ext <;> simp
  ring

theorem spectralBetaLogProfile_fourier_integrable (a b : ℂ) (ha : 0 < a.re) (hb : 0 < b.re) :
    Integrable (𝓕 (spectralBetaLogProfile a b)) := by
  have hpi : (-2*Real.pi : ℝ) ≠ 0 := by positivity
  have hA : Integrable (fun t : ℝ => Complex.Gamma (a-(2*Real.pi*t : ℝ)*Complex.I)) := by
    convert spectral_Gamma_complex_line_integrable a ha (-2*Real.pi) hpi using 1
    ext t
    congr 1
    push_cast
    ring
  have hB : Continuous (fun t : ℝ => Complex.Gamma (b+(2*Real.pi*t : ℝ)*Complex.I)) :=
    spectral_Gamma_complex_line_continuous b hb (2*Real.pi)
  have hp : Integrable (fun t : ℝ => Complex.Gamma (a-(2*Real.pi*t : ℝ)*Complex.I) *
      Complex.Gamma (b+(2*Real.pi*t : ℝ)*Complex.I)) := by
    apply (hA.norm.const_mul (Real.Gamma b.re)).mono' (hA.aestronglyMeasurable.mul hB.aestronglyMeasurable)
    filter_upwards [] with t
    simp only [Pi.mul_apply]
    rw [norm_mul]
    have h := spectral_Gamma_norm_le_real (b+(2*Real.pi*t : ℝ)*Complex.I) (by simpa using hb)
    have h' : ‖Complex.Gamma (b+(2*Real.pi*t : ℝ)*Complex.I)‖ ≤ Real.Gamma b.re := by simpa using h
    nlinarith [mul_le_mul_of_nonneg_left h' (norm_nonneg (Complex.Gamma (a-(2*Real.pi*t : ℝ)*Complex.I)))]
  apply (hp.div_const (Complex.Gamma (a+b))).congr
  filter_upwards [] with t
  exact (spectralBetaLogProfile_fourier_gamma a b ha hb t).symm

end ArtinMatthews
