module

public import ArtinMatthews.SpectralJForwardTransform
public import ArtinMatthews.SpectralWeylMultipliers
public import ArtinMatthews.SpectralWeylGaussianJImaginary
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The positive-real same-sign kernel and the existing Weyl multiplier
have the literal factor x/(4π). The spectral weight is π b_f/cosh(πz). -/
noncomputable section
open Set MeasureTheory Complex

namespace ArtinMatthews

def spectralJForwardSpectralWeight (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  ((Real.pi : ℂ)/Complex.cosh ((Real.pi : ℂ)*z))*spectralJForwardTransform f z

theorem spectralJForwardKernel_real_eq_weyl {r x : ℝ} (hr : 0 < r) (hx : 0 < x) :
    spectralJForwardKernel (r : ℂ) x =
      ((x : ℂ)/(4*(Real.pi : ℂ)))*spectralWeylJMultiplier r x := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsin : Complex.sin ((Real.pi : ℂ)*((r : ℂ)*I)) ≠ 0 := by
    rw [spectral_sin_pi_imaginary]
    exact mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr
      (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hr)).ne')
  rw [spectralJForwardKernel_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
    spectralWeylJMultiplier, ite_eq_left hx, ← spectralWeylJMultiplier_imaginary_coefficient hr,
    show (Real.pi : ℂ)*I*(r : ℂ) = (Real.pi : ℂ)*((r : ℂ)*I) by ring,
    show ((2*r : ℝ) : ℂ)*I = 2*I*(r : ℂ) by push_cast; ring,
    show ((-2*r : ℝ) : ℂ)*I = -2*I*(r : ℂ) by push_cast; ring]
  field_simp [hxC,hπ,hsin] <;> ring

theorem spectralJForwardTransform_real_eq_weyl (f : ℝ → ℂ) {r : ℝ} (hr : 0 < r) :
    spectralJForwardTransform f (r : ℂ) =
      (1/(4*(Real.pi : ℂ)))*(∫ x in Ioi (0 : ℝ), f x*spectralWeylJMultiplier r x) := by
  rw [spectralJForwardTransform, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change f x*spectralJForwardKernel (r : ℂ) x/(x : ℂ) =
    (1/(4*(Real.pi : ℂ)))*(f x*spectralWeylJMultiplier r x)
  rw [spectralJForwardKernel_real_eq_weyl hr hx]
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (show 0 < x from hx).ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hxC,hπ] <;> ring

theorem spectralJForwardSpectralWeight_real_eq_weyl (f : ℝ → ℂ) {r : ℝ} (hr : 0 < r) :
    spectralJForwardSpectralWeight f (r : ℂ) =
      (∫ x in Ioi (0 : ℝ), f x*spectralWeylJMultiplier r x)/
        (4*(Real.cosh (Real.pi*r) : ℂ)) := by
  rw [spectralJForwardSpectralWeight, spectralJForwardTransform_real_eq_weyl f hr,
    ← Complex.ofReal_mul, ← Complex.ofReal_cosh]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hc : (Real.cosh (Real.pi*r) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'
  let total := ∫ x in Ioi (0 : ℝ), f x*spectralWeylJMultiplier r x
  change ((Real.pi : ℂ)/(Real.cosh (Real.pi*r) : ℂ))*
    ((1/(4*(Real.pi : ℂ)))*total) = total/(4*(Real.cosh (Real.pi*r) : ℂ))
  field_simp [hπ,hc] <;> ring

end ArtinMatthews
