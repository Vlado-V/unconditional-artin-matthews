module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import ArtinMatthews.HeckePrimeLogSaving
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

/-! The actual logarithmic transition width costs a fixed logarithmic
power, which is absorbed uniformly by the genuine positive power saving. -/

namespace ArtinMatthews
open Filter

theorem heckeInterval_uniform_power_log_saving (K σ δ A D : ℝ) (k : ℕ)
    (hK : 0 ≤ K) (hσ : σ < 1) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∀ H : ℝ, x^δ ≤ H →
      (K/((Real.log x)^(-D))^k)*H^σ ≤ H*(Real.log x)^(-A) := by
  filter_upwards [heckePrime_uniform_power_log_saving K σ δ (A+D*k) hK hσ hδ,
    eventually_gt_atTop (1 : ℝ)] with x hsave hx
  intro H hH
  have hlog := Real.log_pos hx
  have hden : 0 < ((Real.log x)^(-D))^k := pow_pos (Real.rpow_pos_of_pos hlog _) _
  have hpow : ((Real.log x)^(-D))^k = (Real.log x)^(-(D*k)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlog.le]
    congr 1
    ring
  have heq : (Real.log x)^(-(A+D*k))/((Real.log x)^(-D))^k = (Real.log x)^(-A) := by
    rw [hpow, ← Real.rpow_sub hlog]
    congr 1
    ring
  calc
    _ = (K*H^σ)/((Real.log x)^(-D))^k := by ring
    _ ≤ (H*(Real.log x)^(-(A+D*k)))/((Real.log x)^(-D))^k :=
      div_le_div_of_nonneg_right (hsave H hH) hden.le
    _ = H*((Real.log x)^(-(A+D*k))/((Real.log x)^(-D))^k) := by ring
    _ = _ := by rw [heq]

end ArtinMatthews
