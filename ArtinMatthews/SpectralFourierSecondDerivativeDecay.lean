module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
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

/-! A genuine L1 Fourier bound from two integrable spatial derivatives.
This supplies the Fourier inversion hypothesis for the cosh exponential. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology FourierTransform

namespace ArtinMatthews

theorem spectral_fourier_norm_le_integral_norm (f : ℝ → ℂ) (ξ : ℝ) :
    ‖𝓕 f ξ‖ ≤ ∫ u : ℝ, ‖f u‖ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  calc
    _ ≤ ∫ u : ℝ, ‖Complex.exp (((-2*Real.pi*u*ξ : ℝ) : ℂ)*Complex.I) • f u‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with u
      simp [smul_eq_mul,Complex.norm_exp]

theorem spectral_fourier_second_derivative (f : ℝ → ℂ)
    (hf : Integrable f) (hdf : Differentiable ℝ f) (hf1 : Integrable (deriv f))
    (hdf1 : Differentiable ℝ (deriv f)) (hf2 : Integrable (deriv (deriv f))) (ξ : ℝ) :
    𝓕 (deriv (deriv f)) ξ = (2*(Real.pi : ℂ)*Complex.I*(ξ : ℂ))^2*𝓕 f ξ := by
  rw [congrFun (Real.fourier_deriv hf1 hdf1 hf2) ξ,
    congrFun (Real.fourier_deriv hf hdf hf1) ξ]
  simp only [smul_eq_mul]
  ring

theorem spectral_fourier_quadratic_decay (f : ℝ → ℂ)
    (hf : Integrable f) (hdf : Differentiable ℝ f) (hf1 : Integrable (deriv f))
    (hdf1 : Differentiable ℝ (deriv f)) (hf2 : Integrable (deriv (deriv f))) (ξ : ℝ) :
    ‖𝓕 f ξ‖ ≤ ((∫ u : ℝ, ‖f u‖)+(∫ u : ℝ, ‖deriv (deriv f) u‖)/(4*Real.pi^2))/(1+ξ^2) := by
  have he := congrArg norm (spectral_fourier_second_derivative f hf hdf hf1 hdf1 hf2 ξ)
  have hc : ‖(2*(Real.pi : ℂ)*Complex.I*(ξ : ℂ))^2‖ = 4*Real.pi^2*ξ^2 := by
    simp only [norm_pow,norm_mul,Complex.norm_I,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,mul_one]
    nlinarith [sq_abs ξ]
  rw [norm_mul,hc] at he
  have hb := spectral_fourier_norm_le_integral_norm (deriv (deriv f)) ξ
  have hw : ξ^2*‖𝓕 f ξ‖ ≤ (∫ u : ℝ, ‖deriv (deriv f) u‖)/(4*Real.pi^2) := by
    apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) (sq_pos_of_pos Real.pi_pos))).mpr
    nlinarith
  apply (le_div_iff₀ (show (0 : ℝ) < 1+ξ^2 by positivity)).mpr
  have ha := spectral_fourier_norm_le_integral_norm f ξ
  nlinarith

theorem spectral_fourier_integrable_of_two_derivatives (f : ℝ → ℂ)
    (hf : Integrable f) (hdf : Differentiable ℝ f) (hf1 : Integrable (deriv f))
    (hdf1 : Differentiable ℝ (deriv f)) (hf2 : Integrable (deriv (deriv f))) :
    Integrable (𝓕 f) := by
  have hc : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf
  apply (integrable_inv_one_add_sq.const_mul
    ((∫ u : ℝ, ‖f u‖)+(∫ u : ℝ, ‖deriv (deriv f) u‖)/(4*Real.pi^2))).mono' hc.aestronglyMeasurable
  filter_upwards with ξ
  simpa only [div_eq_mul_inv] using spectral_fourier_quadratic_decay f hf hdf hf1 hdf1 hf2 ξ

end ArtinMatthews
