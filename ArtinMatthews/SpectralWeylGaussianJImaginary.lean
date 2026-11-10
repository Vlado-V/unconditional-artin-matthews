module

public import ArtinMatthews.SpectralWeylDimensionlessKernel
public import Mathlib.Analysis.SpecialFunctions.Bessel
public import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace
public import ArtinMatthews.SpectralWeylGaussianJ
public import ArtinMatthews.SpectralWeylGaussianKAction
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

/-! Principal-series same-sign normalization, with literal 2*pi*i/sinh(pi*r).
The spectral edge r=0 is retained as a separate removable-limit obligation. -/

noncomputable section
open Set MeasureTheory
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectral_sin_pi_imaginary (r : ℝ) :
    Complex.sin ((Real.pi : ℂ)*((r : ℂ)*Complex.I)) =
      Complex.I*(Real.sinh (Real.pi*r) : ℂ) := by
  rw [← mul_assoc,Complex.sin_mul_I,← Complex.ofReal_mul,Complex.ofReal_sinh]
  ring_nf

theorem spectralWeylJMultiplier_imaginary_coefficient {r : ℝ} (hr : 0 < r) :
    -(2 : ℂ)*(Real.pi : ℂ)/Complex.sin ((Real.pi : ℂ)*((r : ℂ)*Complex.I)) =
      (2*(Real.pi : ℂ)*Complex.I)/(Real.sinh (Real.pi*r) : ℂ) := by
  have hs : (Real.sinh (Real.pi*r) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hr)).ne'
  rw [spectral_sin_pi_imaginary]
  field_simp [hs,Complex.I_ne_zero]
  rw [Complex.I_sq]

theorem spectralWeylJMultiplier_imaginary_gaussian {r : ℝ} (hr : 0 < r)
    {p : ℝ} (hp : 0 < p) :
    (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
      (((2*(Real.pi : ℂ)*Complex.I)/(Real.sinh (Real.pi*r) : ℂ))*
        (Complex.besselJ (2*((r : ℂ)*Complex.I)) (X : ℂ)-
          Complex.besselJ (2*(-((r : ℂ)*Complex.I))) (X : ℂ))/(X : ℂ))) =
      2*(Real.sqrt (Real.pi/p) : ℂ)*Complex.exp (-((1/(8*p) : ℝ) : ℂ))*
        schlafliBesselK ((r : ℂ)*Complex.I) (1/(8*p)) := by
  have hν : |((r : ℂ)*Complex.I).re| < 1/2 := by norm_num
  have hsinh : (Real.sinh (Real.pi*r) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hr)).ne'
  have hs : Complex.sin ((Real.pi : ℂ)*((r : ℂ)*Complex.I)) ≠ 0 := by
    rw [spectral_sin_pi_imaginary]
    exact mul_ne_zero Complex.I_ne_zero hsinh
  rw [← spectralWeylJMultiplier_imaginary_coefficient hr]
  exact spectralWeylJMultiplier_gaussian hν hs hp

theorem spectralWeylGaussian_same_K_multiplier {x p r : ℝ} (hx : 0 < x) (hp : 0 < p)
    (hr : 0 < r) (s t : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) (hst : s*t = 1) :
    (∫ z in Ioi (0 : ℝ),
      ((∫ X in Ioi (0 : ℝ), Real.exp (-p*X^2)*X*spectralWeylDimensionlessKernel s t X x z : ℝ) : ℂ)*
        schlafliBesselK ((r : ℂ)*Complex.I) z/(z : ℂ)) =
      schlafliBesselK ((r : ℂ)*Complex.I) x*
        (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
          (((2*(Real.pi : ℂ)*Complex.I)/(Real.sinh (Real.pi*r) : ℂ))*
            (Complex.besselJ (2*((r : ℂ)*Complex.I)) (X : ℂ)-
              Complex.besselJ (2*(-((r : ℂ)*Complex.I))) (X : ℂ))/(X : ℂ))) := by
  rw [spectralWeylGaussian_K_action hx hp s t r hs ht,
    spectralWeylJMultiplier_imaginary_gaussian hr hp,hst]
  push_cast
  ring_nf

end ArtinMatthews
