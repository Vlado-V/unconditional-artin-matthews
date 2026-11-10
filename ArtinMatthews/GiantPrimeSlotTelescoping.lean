module

public import ArtinMatthews.GiantFixedCharacterReplacement
public import ArtinMatthews.PrimeExtractionBilinearExpansion
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Exact prime-slot replacement by the ordinary rough proxy. Both sides
retain the same positive-power cutoff and the original fixed character.
Each telescoping discrepancy is the already proved long-test coefficient. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators

def giantPrimeSlotCoefficient (z : ℝ) (m : ℕ) : ℂ :=
  if z < (m : ℝ) then (if m.Prime then 1 else 0) else 0

def giantRoughSlotCoefficient (W z : ℝ) (m : ℕ) : ℂ :=
  if z < (m : ℝ) then
    (markedSieveEulerProduct W : ℂ)⁻¹ * ((Real.log m)⁻¹ : ℝ) *
      (if ∀ p ∈ Nat.primesLE ⌊W⌋₊, ¬p ∣ m then 1 else 0)
  else 0

theorem giantPrimeSlotCoefficient_eq (z : ℝ) (m : ℕ) :
    giantPrimeSlotCoefficient z m = roughPrimeFirstCoefficient (fun _ => 1) z m := by
  classical
  unfold giantPrimeSlotCoefficient roughPrimeFirstCoefficient
  split_ifs <;> simp_all

/-- The proxy normalization is exactly V(W) inverse times (log m) inverse.
There is no extra log or reciprocal-prime weight in the slot difference. -/
theorem giant_prime_slot_difference (W z : ℝ) (m : ℕ) :
    giantPrimeSlotCoefficient z m - giantRoughSlotCoefficient W z m =
      if z < (m : ℝ) then markedMajorCenteredCoefficient W 0 m else 0 := by
  classical
  unfold giantPrimeSlotCoefficient giantRoughSlotCoefficient markedMajorCenteredCoefficient
  simp only [Complex.ofReal_zero, zero_mul, Complex.cpow_zero, one_mul]
  split_ifs <;> ring

theorem giant_fixed_character_prime_slot_difference {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W z : ℝ) (m : ℕ) :
    χ m * giantPrimeSlotCoefficient z m - χ m * giantRoughSlotCoefficient W z m =
      if z < (m : ℝ) then giantFixedCharacterReplacementCoefficient χ W 0 m else 0 := by
  rw [← mul_sub, giant_prime_slot_difference]
  simp only [mul_ite, mul_zero, giantFixedCharacterReplacementCoefficient]

/-- The finite ordered telescope used when replacing one prime slot at a
time. Earlier slots have already been replaced; later ones are still prime. -/
theorem giant_fixed_character_slots_telescope {j q : ℕ}
    (χ : DirichletCharacter ℂ q) (W z : ℝ) (m : Fin j → ℕ) :
    (∏ i, χ (m i) * giantPrimeSlotCoefficient z (m i)) -
      (∏ i, χ (m i) * giantRoughSlotCoefficient W z (m i)) =
      ∑ i : Fin j,
        (if z < (m i : ℝ) then giantFixedCharacterReplacementCoefficient χ W 0 (m i) else 0) *
        (∏ k : Fin j with k < i, χ (m k) * giantRoughSlotCoefficient W z (m k)) *
        ∏ k : Fin j with i < k, χ (m k) * giantPrimeSlotCoefficient z (m k) := by
  classical
  let a (i : Fin j) := χ (m i) * giantPrimeSlotCoefficient z (m i)
  let b (i : Fin j) := χ (m i) * giantRoughSlotCoefficient W z (m i)
  have h := Finset.prod_sub_ordered Finset.univ a (fun i => a i - b i)
  simp only [sub_sub_cancel] at h
  have heq : (∏ i, a i) - (∏ i, b i) =
      ∑ i : Fin j, (a i-b i) * (∏ k : Fin j with k < i, b k) *
        ∏ k : Fin j with i < k, a k := by
    linear_combination -h
  simpa only [a, b, giant_fixed_character_prime_slot_difference] using heq

/-- A literal finite tuple domain and an arbitrary product-dependent
weight commute with slot replacement. Thus the shifted cutoff and marking
weight may be retained before the analytic hyperbola decomposition. -/
theorem giant_fixed_character_weighted_slots_telescope {j q : ℕ}
    (χ : DirichletCharacter ℂ q) (W z : ℝ) (S : Finset (Fin j → ℕ))
    (w : (Fin j → ℕ) → ℂ) :
    (∑ m ∈ S, w m * ∏ i, χ (m i) * giantPrimeSlotCoefficient z (m i)) -
      (∑ m ∈ S, w m * ∏ i, χ (m i) * giantRoughSlotCoefficient W z (m i)) =
      ∑ i : Fin j, ∑ m ∈ S, w m *
        (if z < (m i : ℝ) then giantFixedCharacterReplacementCoefficient χ W 0 (m i) else 0) *
        (∏ k : Fin j with k < i, χ (m k) * giantRoughSlotCoefficient W z (m k)) *
        ∏ k : Fin j with i < k, χ (m k) * giantPrimeSlotCoefficient z (m k) := by
  rw [← Finset.sum_sub_distrib, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [← mul_sub, giant_fixed_character_slots_telescope, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end ArtinMatthews
