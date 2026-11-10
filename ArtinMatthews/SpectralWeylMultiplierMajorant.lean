module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace
public import ArtinMatthews.SpectralBesselKernelOrderBound
public import ArtinMatthews.SpectralBesselNormalizedOrderBound
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! One actual spectral-order majorant for both literal Weyl multipliers.
The X factor from Gaussian modulus testing is retained and canceled explicitly. -/

noncomputable section
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralWeylKMultiplier_order_majorant {t X : ℝ} (ht : 0 < t) (hX : 0 < X) :
    ‖(X : ℂ)*(8*(Real.cosh (Real.pi*t) : ℂ)*
      schlafliBesselK (2*((t : ℂ)*Complex.I)) X/(X : ℂ))‖ ≤
      4*Real.pi*Real.exp (X^2/4)*(1+(Real.sqrt (Real.cosh Real.pi)/Real.pi)/t) := by
  have hc : 0 ≤ Real.cosh (Real.pi*t) := by linarith [Real.one_le_cosh (Real.pi*t)]
  have he : (X : ℂ)*(8*(Real.cosh (Real.pi*t) : ℂ)*
      schlafliBesselK (2*((t : ℂ)*Complex.I)) X/(X : ℂ)) =
      8*(Real.cosh (Real.pi*t) : ℂ)*schlafliBesselK (2*((t : ℂ)*Complex.I)) X := by
    field_simp [Complex.ofReal_ne_zero.mpr hX.ne']
  rw [he,norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg hc]
  norm_num
  have hb := spectral_besselK_imaginary_order_bound ht hX
  rw [show (((2*t : ℝ) : ℂ)*Complex.I) = 2*((t : ℂ)*Complex.I) by push_cast; ring] at hb
  nlinarith [mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 8)]

theorem spectralWeylJMultiplier_order_majorant {t X : ℝ} (ht : 0 < t) (hX : 0 < X) :
    ‖(X : ℂ)*(((2*(Real.pi : ℂ)*Complex.I)/(Real.sinh (Real.pi*t) : ℂ))*
      (Complex.besselJ (2*((t : ℂ)*Complex.I)) (X : ℂ)-
        Complex.besselJ (2*(-((t : ℂ)*Complex.I))) (X : ℂ))/(X : ℂ))‖ ≤
      4*Real.pi*Real.exp (X^2/4)*(1+(Real.sqrt (Real.cosh Real.pi)/Real.pi)/t) := by
  have hs : 0 < Real.sinh (Real.pi*t) := Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht)
  have hplus := spectral_besselJ_imaginary_order_bound ht hX
  have hminus := spectral_besselJ_neg_imaginary_order_bound ht hX
  have horder : (((2*t : ℝ) : ℂ)*Complex.I) = 2*((t : ℂ)*Complex.I) := by push_cast; ring_nf
  rw [horder] at hplus
  rw [horder,show -(2*((t : ℂ)*Complex.I)) = 2*(-((t : ℂ)*Complex.I)) by ring] at hminus
  have he : (X : ℂ)*(((2*(Real.pi : ℂ)*Complex.I)/(Real.sinh (Real.pi*t) : ℂ))*
      (Complex.besselJ (2*((t : ℂ)*Complex.I)) (X : ℂ)-
        Complex.besselJ (2*(-((t : ℂ)*Complex.I))) (X : ℂ))/(X : ℂ)) =
      ((2*(Real.pi : ℂ)*Complex.I)/(Real.sinh (Real.pi*t) : ℂ))*
        (Complex.besselJ (2*((t : ℂ)*Complex.I)) (X : ℂ)-
          Complex.besselJ (2*(-((t : ℂ)*Complex.I))) (X : ℂ)) := by
    field_simp [Complex.ofReal_ne_zero.mpr hX.ne']
  rw [he,norm_mul,norm_div,norm_mul,norm_mul,Complex.norm_I,mul_one,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs]
  norm_num
  have hd := norm_sub_le (Complex.besselJ (2*((t : ℂ)*Complex.I)) (X : ℂ))
    (Complex.besselJ (2*(-((t : ℂ)*Complex.I))) (X : ℂ))
  have hd' := div_le_div_of_nonneg_right hd hs.le
  have hb : ‖Complex.besselJ (2*((t : ℂ)*Complex.I)) (X : ℂ)-
      Complex.besselJ (2*(-((t : ℂ)*Complex.I))) (X : ℂ)‖/Real.sinh (Real.pi*t) ≤
      2*Real.exp (X^2/4)*(1+(Real.sqrt (Real.cosh Real.pi)/Real.pi)/t) := by
    rw [add_div] at hd'
    linarith
  have hm := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ 2*Real.pi)
  convert hm using 1 <;> ring_nf

end ArtinMatthews
