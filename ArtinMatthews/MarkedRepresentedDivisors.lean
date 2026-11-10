module

public import ArtinMatthews.DivisorWeights
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-!
# Represented divisor unions, including repeated arrays

A selected prime contributes one represented divisor. A pair of selected
primes may coincide: its represented set is `{p,q}`, not a multiset. The
residual damping for a repeated band is consequently `ρ²`.
-/

namespace ArtinMatthews

open scoped BigOperators

noncomputable def representedBandResidual (P S : Finset ℕ) (u a : ℕ) (ρ : ℝ) : ℝ :=
  ∏ p ∈ P \ S, (1 - (1 - ρ ^ a) * (if p ∣ u then 1 else 0))

theorem representedBandResidual_eq (P S : Finset ℕ) (u a : ℕ) (ρ : ℝ) :
    representedBandResidual P S u a ρ =
      (ρ ^ a) ^ ((activeDivisors P u \ S).card) := by
  classical
  have hset : (P \ S).filter (fun p => p ∣ u) = activeDivisors P u \ S := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_sdiff, activeDivisors]
    tauto
  unfold representedBandResidual
  calc
    _ = ∏ p ∈ P \ S, (if p ∣ u then ρ ^ a else 1) := by
      apply Finset.prod_congr rfl
      intro p _
      split_ifs <;> ring
    _ = ∏ _p ∈ (P \ S).filter (fun p => p ∣ u), ρ ^ a := by
      rw [Finset.prod_filter]
    _ = _ := by rw [hset]; simp

noncomputable def representedBandTerm (P S : Finset ℕ) (u a : ℕ) (ρ : ℝ) : ℝ :=
  if S ⊆ activeDivisors P u then
    ρ ^ (a * (S.card - 1)) * representedBandResidual P S u a ρ
  else 0

/-- Once all represented primes divide the argument, the damping equals
the original band's damping, independently of coincidences in the tuple. -/
theorem representedBandTerm_eq_of_subset {P S : Finset ℕ} {u : ℕ}
    (hS : S ⊆ activeDivisors P u) (hne : S.Nonempty) (a : ℕ) (ρ : ℝ) :
    representedBandTerm P S u a ρ = ρ ^ (a * (bandCount P u - 1)) := by
  classical
  have hcard : S.card ≤ (activeDivisors P u).card := Finset.card_le_card hS
  have hpos : 0 < S.card := Finset.card_pos.mpr hne
  rw [representedBandTerm, ite_eq_left hS, representedBandResidual_eq,
    Finset.card_sdiff_of_subset hS, ← pow_mul, ← pow_add, ← Nat.mul_add]
  congr 2
  unfold bandCount
  omega

theorem representedBandTerm_singleton {P : Finset ℕ} {p : ℕ} (hp : p ∈ P)
    (u : ℕ) (ρ : ℝ) :
    representedBandTerm P {p} u 1 ρ =
      if p ∣ u then ρ ^ (bandCount P u - 1) else 0 := by
  classical
  by_cases hpu : p ∣ u
  · rw [ite_eq_left hpu]
    simpa only [one_mul] using representedBandTerm_eq_of_subset
      (P := P) (S := {p}) (u := u)
      (by simpa [activeDivisors] using And.intro hp hpu)
      (Finset.singleton_nonempty p) 1 ρ
  · rw [ite_eq_right hpu, representedBandTerm, ite_eq_right]
    simpa [activeDivisors, hp] using hpu

theorem representedBandTerm_pair {P : Finset ℕ} {p q : ℕ}
    (hp : p ∈ P) (hq : q ∈ P) (u : ℕ) (ρ : ℝ) :
    representedBandTerm P {p, q} u 2 ρ =
      if p ∣ u ∧ q ∣ u then ρ ^ (2 * (bandCount P u - 1)) else 0 := by
  classical
  have hsubset : {p, q} ⊆ activeDivisors P u ↔ p ∣ u ∧ q ∣ u := by
    simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, activeDivisors, hp, hq]
  by_cases hpu : p ∣ u ∧ q ∣ u
  · rw [ite_eq_left hpu]
    exact representedBandTerm_eq_of_subset
      (hsubset.mpr hpu)
      (by simp) 2 ρ
  · rw [ite_eq_right hpu, representedBandTerm, ite_eq_right]
    exact fun h => hpu (hsubset.mp h)

/-- Exact represented-prime expansion for one band. -/
theorem bandWeight_eq_represented_single_sum (P : Finset ℕ) (V : ℝ) (u : ℕ) :
    bandWeight P V u =
      (∑ p ∈ P, representedBandTerm P {p} u 1 (1 / 2)) / V := by
  classical
  have hsum : (∑ p ∈ P, representedBandTerm P {p} u 1 (1 / 2)) =
      (bandCount P u : ℝ) * (1 / 2 : ℝ) ^ (bandCount P u - 1) := by
    calc
      _ = ∑ p ∈ P, if p ∣ u then (1 / 2 : ℝ) ^ (bandCount P u - 1) else 0 :=
        Finset.sum_congr rfl (fun p hp => representedBandTerm_singleton hp u (1 / 2))
      _ = _ := by rw [← Finset.sum_filter]; simp [activeDivisors, bandCount]
  rw [hsum]
  rfl

/-- Exact represented-prime expansion for a repeated band. Coincident
selected primes are retained and use a singleton represented union. -/
theorem bandWeight_sq_eq_represented_pair_sum (P : Finset ℕ) (V : ℝ) (u : ℕ) :
    (bandWeight P V u) ^ 2 =
      (∑ p ∈ P, ∑ q ∈ P, representedBandTerm P {p, q} u 2 (1 / 2)) / V ^ 2 := by
  classical
  have hsum : (∑ p ∈ P, ∑ q ∈ P, representedBandTerm P {p, q} u 2 (1 / 2)) =
      (bandCount P u : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (2 * (bandCount P u - 1)) := by
    calc
      _ = ∑ p ∈ P, ∑ q ∈ P,
          if p ∣ u ∧ q ∣ u then (1 / 2 : ℝ) ^ (2 * (bandCount P u - 1)) else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        exact Finset.sum_congr rfl (fun q hq => representedBandTerm_pair hp hq u (1 / 2))
      _ = _ := by
        simp_rw [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
        rw [← Finset.sum_filter, ← Finset.sum_filter]
        simp [activeDivisors, bandCount, pow_two, mul_assoc]
  rw [hsum]
  unfold bandWeight halfDampedCount
  rw [div_pow, mul_pow]
  congr 2
  rw [← pow_mul, Nat.mul_comm]

end ArtinMatthews
