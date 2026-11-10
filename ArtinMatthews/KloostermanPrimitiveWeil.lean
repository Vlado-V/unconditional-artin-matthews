module

public import OAI.NumberTheory.Jacobsthal.Estimates.PairCollisionCount
public import ArtinMatthews.KloostermanEvenDyadicBound
public import ArtinMatthews.KloostermanOddPrimeBound
public import ArtinMatthews.KloostermanPrimeWeilTransfer
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

/-! Genuine primitive square-root bounds for every positive prime-power exponent. -/
noncomputable section
open OAI.Erdos970.ErdosKloosterman
namespace ArtinMatthews.PrimePowerWeil

theorem standardSum_primitive_power_ge_two (p a : ℕ) [Fact p.Prime] (ha : 2 ≤ a)
    (h k : ℤ) (hnot : (h:ZMod p) ≠ 0 ∨ (k:ZMod p) ≠ 0) :
    ‖standardSum (p^a) h k‖≤8*Real.sqrt ((p^a:ℕ):ℝ) := by
  let m := a/2
  have he : a=2*m ∨ a=2*m+1 := by dsimp [m]; omega
  rcases he with he | he
  · have hm : 0 < m := by omega
    rw [he]
    exact (standardSum_even_prime_power p m hm h k hnot).trans
      (mul_le_mul_of_nonneg_right (by norm_num : (4:ℝ) ≤ 8) (Real.sqrt_nonneg _))
  · have hm : 1 ≤ m := by omega
    rw [he]
    by_cases hp2 : p=2
    · subst p
      exact standardSum_dyadic_odd_power m hm h k hnot
    · exact (standardSum_odd_prime_power p m hm hp2 h k hnot).trans
        (mul_le_mul_of_nonneg_right (by norm_num : (2:ℝ) ≤ 8) (Real.sqrt_nonneg _))

theorem standardSum_primitive_prime_power (p a : ℕ) [Fact p.Prime] (ha : 0 < a)
    (h k : ℤ) (hnot : (h:ZMod p) ≠ 0 ∨ (k:ZMod p) ≠ 0) :
    ‖standardSum (p^a) h k‖≤8*Real.sqrt ((p^a:ℕ):ℝ) := by
  by_cases ha1 : a=1
  · subst a
    have hb := standardSum_prime_weil_bound p h k hnot
    have hc : 2*Real.sqrt (p:ℝ) ≤ 8*Real.sqrt p :=
      mul_le_mul_of_nonneg_right (by norm_num : (2:ℝ) ≤ 8) (Real.sqrt_nonneg _)
    simpa only [pow_one] using hb.trans hc
  · exact standardSum_primitive_power_ge_two p a (by omega) h k hnot

end ArtinMatthews.PrimePowerWeil
