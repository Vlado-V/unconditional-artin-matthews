module

public import OAI.NumberTheory.Jacobsthal.Estimates.PairCollisionCount
public import ArtinMatthews.KloostermanOddPowerGauss
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import OAI.NumberTheory.Jacobsthal.Estimates.PrimitiveThreeQuarters


set_option backward.privateInPublic true
@[expose] public section

/-! The actual primitive odd prime-power Kloosterman sum has its square-root bound. -/
noncomputable section
open scoped BigOperators
open OAI.Erdos970.ErdosKloosterman OAI.Erdos970.ErdosKloosterman.PrimePower
namespace ArtinMatthews.PrimePowerWeil

attribute [local instance] Classical.decEq

theorem oddPower_sqrt (p m : ℕ) :
    Real.sqrt ((p^(2*m+1):ℕ):ℝ)=((p^m:ℕ):ℝ)*Real.sqrt p := by
  have he : p^(2*m+1)=(p^m)^2*p := by
    rw [← pow_mul,← pow_succ]
    congr 1
    omega
  rw [he,Nat.cast_mul,Nat.cast_pow,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (Nat.cast_nonneg _)]

theorem standardSum_odd_prime_power_left (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hp2 : p ≠ 2)
    (h k : ℤ) (hh : (h:ZMod p)≠0) :
    ‖standardSum (p^(2*m+1)) h k‖≤2*Real.sqrt ((p^(2*m+1):ℕ):ℝ) := by
  have ha : oddPowerReduction p m (h:OddPowerRing p m)≠0 := by
    simpa only [map_intCast] using hh
  have havg := oddPower_averaged_norm p m hm hp2 (h:OddPowerRing p m) (k:OddPowerRing p m) ha
  have hc : ((stationaryUnits ((p^(m+1):ℕ):OddPowerRing p m) (h:OddPowerRing p m) k).card:ℝ)≤
      2*((p^(m+1):ℕ):ℝ) := by
    exact_mod_cast oddPower_stationary_card p m (by omega) hp2 h k hh
  have hp : 0<(p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hprod : ‖sum ZMod.stdAddChar (h:OddPowerRing p m) (k:OddPowerRing p m)‖≤
      2*((p^m:ℕ):ℝ)*Real.sqrt p := by
    apply (mul_le_mul_iff_right₀ hp).mp
    calc
      _ ≤ ((stationaryUnits ((p^(m+1):ℕ):OddPowerRing p m) (h:OddPowerRing p m) k).card:ℝ)*Real.sqrt p := havg
      _ ≤ (2*((p^(m+1):ℕ):ℝ))*Real.sqrt p := mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)
      _ = (p:ℝ)*(2*((p^m:ℕ):ℝ)*Real.sqrt p) := by
        rw [pow_succ p m,Nat.cast_mul]
        ring
  have hN : p^(2*m+1)=p^(m+1)*p^m := by
    rw [← pow_add]
    congr 1
    omega
  rw [standardSum_modulus_congr _ _ hN,oddPower_sqrt]
  simpa only [standardSum,mul_assoc] using hprod

theorem standardSum_odd_prime_power (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hp2 : p ≠ 2)
    (h k : ℤ) (hnot : (h:ZMod p)≠0 ∨ (k:ZMod p)≠0) :
    ‖standardSum (p^(2*m+1)) h k‖≤2*Real.sqrt ((p^(2*m+1):ℕ):ℝ) := by
  rcases hnot with hh | hk
  · exact standardSum_odd_prime_power_left p m hm hp2 h k hh
  · rw [show standardSum (p^(2*m+1)) h k=standardSum (p^(2*m+1)) k h from
      sum_swap ZMod.stdAddChar (h:ZMod (p^(2*m+1))) (k:ZMod (p^(2*m+1)))]
    exact standardSum_odd_prime_power_left p m hm hp2 k h hk

end ArtinMatthews.PrimePowerWeil
