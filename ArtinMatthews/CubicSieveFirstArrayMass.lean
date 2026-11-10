module

public import ArtinMatthews.MarkedArrayEulerModel
public import ArtinMatthews.CubicSamplingArrayTruncation
public import ArtinMatthews.MarkedArrayReciprocalBounds
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

/-! Exact reciprocal selected-prime mass for a genuine first marking array. -/

noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators

theorem cubicSieve_firstArray_selected_card {J : Type*} [Fintype J]
    (t : (j : J) → Fin 1 → ℕ) : (representedArraySelected t).card ≤ Fintype.card J := by
  simpa only [sum_const, card_univ, smul_eq_mul, mul_one] using
    cubicSampling_selected_card_le (a := fun _ : J => 1) t

theorem cubicSieve_firstArray_coefficient {J : Type*} [Fintype J]
    (V : J → ℝ) (t : (j : J) → Fin 1 → ℕ) :
    representedArrayCoefficient V (fun _ => 1) t = 1 / ∏ j, V j := by
  simp only [representedArrayCoefficient, representedChoiceSet_one, card_singleton,
    Nat.sub_self, mul_zero, pow_zero, prod_const_one, pow_one]

theorem cubicSieve_firstArray_reciprocal_mass {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) :
    (∑ t ∈ representedArrayChoices P (fun _ => 1),
      representedArrayCoefficient (fun j => bandReciprocalMass (P j)) (fun _ => 1) t *
        ∏ p ∈ representedArraySelected t, (1 : ℝ) / p) = 1 := by
  have h := represented_array_normalized_reciprocal_mass P (fun j => bandReciprocalMass (P j))
    (fun j => (hV j).le) (fun _ => 1) hdis
  have hrhs : (∏ j, representedTupleReciprocalMass (P j) 1 (1 / 2) /
      bandReciprocalMass (P j) ^ 1) = (1 : ℝ) := by
    simp only [representedTupleReciprocalMass_one, pow_one, div_self (hV _).ne', prod_const_one]
  rw [hrhs] at h
  convert h using 1
  apply sum_congr rfl
  intro t _
  rw [abs_of_nonneg (representedArrayCoefficient_nonneg _ (fun j => (hV j).le) _ t),
    prod_div_distrib, prod_const_one, ← Nat.cast_prod]
  ring

theorem cubicSieve_firstArray_selected_mass_le_one {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (g : ℕ → ℝ)
    (hg : ∀ p ∈ Finset.univ.biUnion P, 0 ≤ g p ∧ g p ≤ 1 / (p : ℝ)) :
    (∑ t ∈ representedArrayChoices P (fun _ => 1),
      representedArrayCoefficient (fun j => bandReciprocalMass (P j)) (fun _ => 1) t *
        ∏ p ∈ representedArraySelected t, g p) ≤ 1 := by
  rw [← cubicSieve_firstArray_reciprocal_mass P hdis hV]
  apply sum_le_sum
  intro t ht
  have hS := cubicSampling_selected_subset P (fun _ => 1) ht
  apply mul_le_mul_of_nonneg_left _
    (representedArrayCoefficient_nonneg _ (fun j => (hV j).le) _ t)
  exact prod_le_prod₀ (fun p hp => (hg p (hS hp)).1) (fun p hp => (hg p (hS hp)).2)

end ArtinMatthews
