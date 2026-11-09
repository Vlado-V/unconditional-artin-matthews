module

public import ArtinMatthews.MarkedArrayReciprocalBounds
public import ArtinMatthews.CubicSamplingArrayTruncation


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
