module

public import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace
public import ArtinMatthews.SpectralWeberK
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

/-! Real square-root and imaginary-order normalizations of the proved
Gaussian Weber K evaluation. -/

noncomputable section
open Set MeasureTheory
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectral_positive_cpow_neg_half {p : ℝ} (hp : 0 < p) :
    (p : ℂ)^(-(1/2 : ℂ)) = (Real.sqrt p : ℂ)⁻¹ := by
  rw [show (-(1/2 : ℂ)) = ((-(1/2 : ℝ)) : ℂ) by norm_num,
    ← Complex.ofReal_neg,← Complex.ofReal_cpow hp.le,Real.rpow_neg hp.le,← Real.sqrt_eq_rpow,
    Complex.ofReal_inv]

theorem schlafliBesselK_gaussian_weber {ν : ℂ} (hν : |ν.re| < 1/2)
    {p : ℝ} (hp : 0 < p) :
    (∫ x in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(x : ℂ)^2)*schlafliBesselK (2*ν) x) =
      ((Real.sqrt (Real.pi/p) : ℂ)/(4*Complex.cos ((Real.pi : ℂ)*ν)))*
        Complex.exp ((1/(8*p) : ℝ) : ℂ)*schlafliBesselK ν (1/(8*p)) := by
  rw [spectralWeberK_evaluation hν hp,spectral_positive_cpow_neg_half hp,
    show (1/8 : ℝ)/p = 1/(8*p) by simp only [div_eq_mul_inv,mul_inv,one_mul]]
  have hr : (Real.sqrt (Real.pi/p) : ℂ) = (Real.sqrt Real.pi : ℂ)/(Real.sqrt p : ℂ) := by
    rw [Real.sqrt_div Real.pi_pos.le,Complex.ofReal_div]
  rw [hr]
  ring

theorem schlafliBesselK_imaginary_gaussian_weber (r : ℝ) {p : ℝ} (hp : 0 < p) :
    (∫ x in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(x : ℂ)^2)*
      schlafliBesselK (2*((r : ℂ)*Complex.I)) x) =
      ((Real.sqrt (Real.pi/p) : ℂ)/(4*(Real.cosh (Real.pi*r) : ℂ)))*
        Complex.exp ((1/(8*p) : ℝ) : ℂ)*schlafliBesselK ((r : ℂ)*Complex.I) (1/(8*p)) := by
  have hν : |((r : ℂ)*Complex.I).re| < 1/2 := by norm_num
  have hc : Complex.cos ((Real.pi : ℂ)*((r : ℂ)*Complex.I)) =
      (Real.cosh (Real.pi*r) : ℂ) := by
    rw [← mul_assoc,Complex.cos_mul_I,← Complex.ofReal_mul,Complex.ofReal_cosh]
  rw [schlafliBesselK_gaussian_weber hν hp,hc]

end ArtinMatthews
