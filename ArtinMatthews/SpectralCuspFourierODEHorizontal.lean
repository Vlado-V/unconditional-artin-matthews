module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! Literal integer-frequency phases and genuine periodic integration by
parts on a full horizontal period. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace ArtinMatthews

def cuspFourierFrequency (w : ℝ) (n : ℤ) : ℝ := 2 * Real.pi * n / w

def cuspFourierPhase (w : ℝ) (n : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (-((cuspFourierFrequency w n : ℝ) : ℂ) * Complex.I * x)

theorem cuspFourierPhase_contDiff (w : ℝ) (n : ℤ) : ContDiff ℝ ∞ (cuspFourierPhase w n) := by
  unfold cuspFourierPhase
  exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

theorem cuspFourierPhase_hasDerivAt (w : ℝ) (n : ℤ) (x : ℝ) :
    HasDerivAt (cuspFourierPhase w n)
      (cuspFourierPhase w n x * (-((cuspFourierFrequency w n : ℝ) : ℂ) * Complex.I)) x := by
  simpa only [cuspFourierPhase, id_eq, Complex.ofReal_one, mul_one] using!
    (((hasDerivAt_id x).ofReal_comp).const_mul
      (-((cuspFourierFrequency w n : ℝ) : ℂ) * Complex.I)).cexp

theorem cuspFourierPhase_zero (w : ℝ) (n : ℤ) : cuspFourierPhase w n 0 = 1 := by
  simp only [cuspFourierPhase, Complex.ofReal_zero, mul_zero, Complex.exp_zero]

theorem cuspFourierPhase_period (w : ℝ) (hw : 0 < w) (n : ℤ) : cuspFourierPhase w n w = 1 := by
  have he : -((cuspFourierFrequency w n : ℝ) : ℂ) * Complex.I * (w : ℂ) =
      ((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    unfold cuspFourierFrequency
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hw.ne']
  rw [cuspFourierPhase, he]
  exact Complex.exp_int_mul_two_pi_mul_I (-n)

theorem spectral_periodic_deriv {f : ℝ → ℂ} {w : ℝ} (h : Function.Periodic f w) :
    Function.Periodic (deriv f) w := by
  intro x
  have he : (fun t => f (t + w)) = f := funext h
  simpa only [deriv_comp_add_const] using congrArg (fun g : ℝ → ℂ => deriv g x) he

theorem cuspFourier_integral_deriv (w : ℝ) (hw : 0 < w) (n : ℤ)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f w) :
    (∫ x in (0 : ℝ)..w, cuspFourierPhase w n x * deriv f x) =
      (((cuspFourierFrequency w n : ℝ) : ℂ) * Complex.I) *
        (∫ x in (0 : ℝ)..w, cuspFourierPhase w n x * f x) := by
  have hχ := cuspFourierPhase_contDiff w n
  have hd := (contDiff_infty_iff_deriv.mp hf).2
  have he := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ => cuspFourierPhase_hasDerivAt w n x)
    (fun x _ => (hf.differentiable (by simp) x).hasDerivAt)
    ((hχ.continuous.mul continuous_const).intervalIntegrable 0 w)
    (hd.continuous.intervalIntegrable 0 w)
  rw [cuspFourierPhase_period w hw n, cuspFourierPhase_zero, one_mul, one_mul,
    show f w = f 0 by simpa only [zero_add] using hp 0, sub_self, zero_sub] at he
  have hfactor :
      (∫ x in (0 : ℝ)..w, (cuspFourierPhase w n x *
        (-((cuspFourierFrequency w n : ℝ) : ℂ) * Complex.I)) * f x) =
      (-((cuspFourierFrequency w n : ℝ) : ℂ) * Complex.I) *
        (∫ x in (0 : ℝ)..w, cuspFourierPhase w n x * f x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hfactor] at he
  simpa only [neg_mul, neg_neg] using he

theorem cuspFourier_integral_second_deriv (w : ℝ) (hw : 0 < w) (n : ℤ)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f w) :
    (∫ x in (0 : ℝ)..w, cuspFourierPhase w n x * deriv (deriv f) x) =
      -(((cuspFourierFrequency w n : ℝ) : ℂ) ^ 2 *
        (∫ x in (0 : ℝ)..w, cuspFourierPhase w n x * f x)) := by
  rw [cuspFourier_integral_deriv w hw n (deriv f) (contDiff_infty_iff_deriv.mp hf).2
      (spectral_periodic_deriv hp), cuspFourier_integral_deriv w hw n f hf hp]
  calc
    _ = (((cuspFourierFrequency w n : ℝ) : ℂ) ^ 2 * Complex.I ^ 2) *
        (∫ x in (0 : ℝ)..w, cuspFourierPhase w n x * f x) := by ring
    _ = _ := by rw [Complex.I_sq]; ring

end ArtinMatthews
