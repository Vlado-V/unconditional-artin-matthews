module

public import ArtinMatthews.SpectralKLDirectDefinitions
public import ArtinMatthews.SpectralBesselKIConnection
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

namespace ArtinMatthews
open Set MeasureTheory OAI.CubicEisenstein
noncomputable section

theorem spectralKLDirectIIntegrand_pair (F : ℂ → ℂ)
    (heven : ∀ z : ℂ, F (-z) = F z)
    {x : ℝ} (hx : 0 < x) (t : ℝ) :
    spectralKLDirectIIntegrand F x (t : ℂ) + spectralKLDirectIIntegrand F x (-t : ℂ) =
      ((Real.pi : ℂ) * Complex.I) *
        (schlafliBesselK ((t : ℂ) * Complex.I) x * F (t : ℂ) *
          (spectralKLPlancherelWeight t : ℂ)) := by
  have harg' : -Complex.I * (-(t : ℂ)) = (t : ℂ) * Complex.I := by ring
  have harg'' : -Complex.I * (t : ℂ) = -((t : ℂ) * Complex.I) := by ring
  have hs : Complex.sin ((Real.pi : ℂ) * ((t : ℂ) * Complex.I)) =
      ((Real.sinh (Real.pi * t) : ℝ) : ℂ) * Complex.I := by
    rw [← mul_assoc, ← Complex.ofReal_mul, Complex.sin_mul_I, Complex.ofReal_sinh]
  have hconn := schlafliBesselK_eq_I_difference
    (ν := (t : ℂ) * Complex.I) (by simp) hx
  have hdiff : spectralBesselI (-((t : ℂ) * Complex.I)) x -
      spectralBesselI ((t : ℂ) * Complex.I) x =
        (2 / (Real.pi : ℂ)) * ((Real.sinh (Real.pi * t) : ℝ) : ℂ) * Complex.I *
          schlafliBesselK ((t : ℂ) * Complex.I) x := by
    rw [hs] at hconn
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    apply (mul_left_cancel₀ (show (Real.pi : ℂ) / 2 ≠ 0 by exact div_ne_zero hpi (by norm_num)))
    calc
      _ = ((Real.sinh (Real.pi * t) : ℝ) : ℂ) * Complex.I *
          schlafliBesselK ((t : ℂ) * Complex.I) x := hconn.symm
      _ = _ := by field_simp
  unfold spectralKLDirectIIntegrand
  rw [harg', harg'', heven]
  calc
    _ = (t : ℂ) * F (t : ℂ) *
        (spectralBesselI (-((t : ℂ) * Complex.I)) x - spectralBesselI ((t : ℂ) * Complex.I) x) := by ring
    _ = _ := by
      rw [hdiff]
      unfold spectralKLPlancherelWeight
      push_cast
      field_simp


end
end ArtinMatthews
