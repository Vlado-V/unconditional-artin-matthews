module

public import ArtinMatthews.SpectralBesselI
public import ArtinMatthews.SpectralBesselIOrderBound
public import ArtinMatthews.SpectralBesselOrderSmall
public import ArtinMatthews.SpectralBesselSeriesOrderBound
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! The actual J/I order bounds after the literal sinh normalization.
The majorant is bounded at infinity and only O(1/t) at the spectral edge. -/

noncomputable section

namespace ArtinMatthews

theorem spectral_Bessel_sinh_rescale_bound {t A E : ℝ} (ht : 0 < t) (hE : 0 ≤ E)
    (hA : A ≤ E/‖Complex.Gamma (1+((2*t : ℝ) : ℂ)*Complex.I)‖) :
    A/Real.sinh (Real.pi*t) ≤ E*(1+(Real.sqrt (Real.cosh Real.pi)/Real.pi)/t) := by
  have hs : 0 < Real.sinh (Real.pi*t) := Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht)
  calc
    _ ≤ (E/‖Complex.Gamma (1+((2*t : ℝ) : ℂ)*Complex.I)‖)/Real.sinh (Real.pi*t) :=
      div_le_div_of_nonneg_right hA hs.le
    _ = E*(1/spectralBesselOrderDenominator t) := by
      unfold spectralBesselOrderDenominator
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (spectralBesselOrderFactor_bound ht) hE

theorem spectral_besselJ_imaginary_order_bound {t X : ℝ} (ht : 0 < t) (hX : 0 < X) :
    ‖Complex.besselJ (((2*t : ℝ) : ℂ)*Complex.I) (X : ℂ)‖/Real.sinh (Real.pi*t) ≤
      Real.exp (X^2/4)*(1+(Real.sqrt (Real.cosh Real.pi)/Real.pi)/t) := by
  apply spectral_Bessel_sinh_rescale_bound ht (Real.exp_pos _).le
  have h := spectral_besselJ_norm_le_exp_of_re_zero (((2*t : ℝ) : ℂ)*Complex.I) (by simp) hX
  simpa only [add_comm] using h

theorem spectral_besselI_imaginary_order_bound {t X : ℝ} (ht : 0 < t) (hX : 0 < X) :
    ‖spectralBesselI (((2*t : ℝ) : ℂ)*Complex.I) X‖/Real.sinh (Real.pi*t) ≤
      Real.exp (X^2/4)*(1+(Real.sqrt (Real.cosh Real.pi)/Real.pi)/t) := by
  apply spectral_Bessel_sinh_rescale_bound ht (Real.exp_pos _).le
  have h := spectralBesselI_norm_le_exp_of_re_zero (((2*t : ℝ) : ℂ)*Complex.I) (by simp) hX
  simpa only [add_comm] using h

end ArtinMatthews
