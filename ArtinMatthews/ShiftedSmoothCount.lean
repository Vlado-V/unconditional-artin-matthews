module

public import ArtinMatthews.ShiftedSmoothRankin
public import ArtinMatthews.ShiftedSmoothEulerBound
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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


set_option backward.privateInPublic true
@[expose] public section

/-! The precise uniform smooth-support count used for the admissible
common-prime parts in the shifted bilinear summation. -/
namespace ArtinMatthews
open scoped BigOperators

/-- The number of positive D≤B supported on the prime divisors of d is
at most Cε B^ε d^ε, uniformly in both B and d. -/
theorem shiftedSmooth_count_subpower (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ B d : ℕ, 0<d →
      ((shiftedSmoothSet B d.primeFactors).card : ℝ) ≤
        C*(B : ℝ)^ε*(d : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := shiftedSmooth_euler_subpower ε hε
  refine ⟨C,hC,?_⟩
  intro B d hd
  have hfilter : d.primeFactors.filter Nat.Prime=d.primeFactors := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    exact Nat.prime_of_mem_primeFactors hp
  have h := shiftedSmooth_rankin B d.primeFactors ε hε
  rw [hfilter] at h
  calc
    _ ≤ (B : ℝ)^ε*∏ p∈d.primeFactors,(1-(p:ℝ)^(-ε))⁻¹ := h
    _ ≤ (B : ℝ)^ε*(C*(d : ℝ)^ε) :=
      mul_le_mul_of_nonneg_left (hbound d hd) (Real.rpow_nonneg (Nat.cast_nonneg B) ε)
    _ = _ := by ring

end ArtinMatthews
