module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace
public import ArtinMatthews.SpectralBesselKIConnection
public import ArtinMatthews.SpectralWeberJ
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
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Actual same-sign J multiplier under Gaussian modulus testing.
The divided multiplier requires sin(pi*nu) != 0; the undivided difference
identity also includes zero order. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralWeberJ_difference {ν : ℂ} (hν : |ν.re| < 1/2)
    {p : ℝ} (hp : 0 < p) :
    (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*
      (Complex.besselJ (2*ν) (X : ℂ)-Complex.besselJ (2*(-ν)) (X : ℂ))) =
      (-(2 : ℂ)/(Real.pi : ℂ))*((Real.sqrt (Real.pi/p) : ℂ)/2)*
        Complex.exp (-((1/(8*p) : ℝ) : ℂ))*Complex.sin ((Real.pi : ℂ)*ν)*
        schlafliBesselK ν (1/(8*p)) := by
  have hpos : -(1/2 : ℝ) < ν.re := by linarith [neg_le_abs ν.re]
  have hneg : -(1/2 : ℝ) < (-ν).re := by simp only [Complex.neg_re]; linarith [le_abs_self ν.re]
  have hv : 0 < 1/(8*p) := one_div_pos.mpr (by positivity)
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI := schlafliBesselK_eq_I_difference hν hv
  rw [mul_comm (Real.pi : ℂ) ν] at hI
  have hd : spectralBesselI ν (1/(8*p))-spectralBesselI (-ν) (1/(8*p)) =
      (-(2 : ℂ)/(Real.pi : ℂ))*(Complex.sin ((Real.pi : ℂ)*ν)*schlafliBesselK ν (1/(8*p))) := by
    apply mul_right_cancel₀ hpi
    field_simp [hpi]
    linear_combination 2*hI
  simp_rw [mul_sub]
  rw [integral_sub (spectralWeberJ_integrable ν hpos hp) (spectralWeberJ_integrable (-ν) hneg hp),
    spectralBesselJ_gaussian_weber ν hpos hp,spectralBesselJ_gaussian_weber (-ν) hneg hp]
  calc
    _ = (((Real.sqrt (Real.pi/p) : ℂ)/2)*Complex.exp (-((1/(8*p) : ℝ) : ℂ)))*
        (spectralBesselI ν (1/(8*p))-spectralBesselI (-ν) (1/(8*p))) := by ring
    _ = _ := by rw [hd]; ring

theorem spectralWeylJMultiplier_gaussian_integrable {ν : ℂ} (hν : |ν.re| < 1/2)
    {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun X : ℝ => Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
      ((-(2 : ℂ)*(Real.pi : ℂ)/Complex.sin ((Real.pi : ℂ)*ν))*
        (Complex.besselJ (2*ν) (X : ℂ)-Complex.besselJ (2*(-ν)) (X : ℂ))/(X : ℂ)))
      (Ioi (0 : ℝ)) := by
  have hpos : -(1/2 : ℝ) < ν.re := by linarith [neg_le_abs ν.re]
  have hneg : -(1/2 : ℝ) < (-ν).re := by simp only [Complex.neg_re]; linarith [le_abs_self ν.re]
  have hi := ((spectralWeberJ_integrable ν hpos hp).sub
    (spectralWeberJ_integrable (-ν) hneg hp)).const_mul
      (-(2 : ℂ)*(Real.pi : ℂ)/Complex.sin ((Real.pi : ℂ)*ν))
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
  dsimp only [Pi.sub_apply]
  field_simp [Complex.ofReal_ne_zero.mpr hX.ne']

theorem spectralWeylJMultiplier_gaussian {ν : ℂ} (hν : |ν.re| < 1/2)
    (hsin : Complex.sin ((Real.pi : ℂ)*ν) ≠ 0) {p : ℝ} (hp : 0 < p) :
    (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
      ((-(2 : ℂ)*(Real.pi : ℂ)/Complex.sin ((Real.pi : ℂ)*ν))*
        (Complex.besselJ (2*ν) (X : ℂ)-Complex.besselJ (2*(-ν)) (X : ℂ))/(X : ℂ))) =
      2*(Real.sqrt (Real.pi/p) : ℂ)*Complex.exp (-((1/(8*p) : ℝ) : ℂ))*
        schlafliBesselK ν (1/(8*p)) := by
  have he : (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
      ((-(2 : ℂ)*(Real.pi : ℂ)/Complex.sin ((Real.pi : ℂ)*ν))*
        (Complex.besselJ (2*ν) (X : ℂ)-Complex.besselJ (2*(-ν)) (X : ℂ))/(X : ℂ))) =
      (-(2 : ℂ)*(Real.pi : ℂ)/Complex.sin ((Real.pi : ℂ)*ν))*
        (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*
          (Complex.besselJ (2*ν) (X : ℂ)-Complex.besselJ (2*(-ν)) (X : ℂ))) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro X hX
    dsimp only
    field_simp [Complex.ofReal_ne_zero.mpr hX.ne']
  rw [he,spectralWeberJ_difference hν hp]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hpi,hsin]

end ArtinMatthews
