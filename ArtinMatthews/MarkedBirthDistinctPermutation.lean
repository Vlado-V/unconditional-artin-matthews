module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Type


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite birth-distinctness inclusion-exclusion. An unperformed
potential address has value none and is forced to remain fixed. The
determinant expansion counts signed cycle systems without assigning a
prime value to an unperformed address. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def MarkedPerformedInjective {A P : Type*} (p : A → Option P) : Prop :=
  Set.InjOn p {a | p a ≠ none}

def markedBirthEqualityMatrix {A P : Type*} [Fintype A] [DecidableEq A]
    (p : A → Option P) : Matrix A A ℤ :=
  fun a b => if a = b ∨ p a ≠ none ∧ p a = p b then 1 else 0

theorem markedBirthEqualityMatrix_of_injective
    {A P : Type*} [Fintype A] [DecidableEq A] (p : A → Option P)
    (hp : MarkedPerformedInjective p) : markedBirthEqualityMatrix p = 1 := by
  ext a b
  by_cases hab : a = b
  · subst b
    simp [markedBirthEqualityMatrix]
  · have hno : ¬(p a ≠ none ∧ p a = p b) := by
      rintro ⟨ha,h⟩
      have hb : p b ≠ none := fun hb => ha (h.trans hb)
      exact hab (hp ha hb h)
    simp [markedBirthEqualityMatrix, hab, hno]

theorem markedBirthEqualityMatrix_performed_row
    {A P : Type*} [Fintype A] [DecidableEq A] (p : A → Option P)
    (a : A) (ha : p a ≠ none) :
    markedBirthEqualityMatrix p a = fun b => if p a = p b then 1 else 0 := by
  funext b
  by_cases hp : p a = p b
  · exact (ite_eq_left (Or.inr ⟨ha,hp⟩)).trans (ite_eq_left hp).symm
  · have hab : a ≠ b := fun h => hp (congrArg p h)
    simp [markedBirthEqualityMatrix, hp, hab]

theorem markedBirthEqualityMatrix_det
    {A P : Type*} [Fintype A] [DecidableEq A] (p : A → Option P) :
    (markedBirthEqualityMatrix p).det = if MarkedPerformedInjective p then 1 else 0 := by
  by_cases hp : MarkedPerformedInjective p
  · rw [ite_eq_left hp, markedBirthEqualityMatrix_of_injective p hp, Matrix.det_one]
  · rw [ite_eq_right hp]
    have hn : ¬Set.InjOn p {a | p a ≠ none} := hp
    simp only [Set.InjOn, Set.mem_ofPred_eq] at hn
    push Not at hn
    obtain ⟨a,ha,b,hb,heq,hab⟩ := hn
    apply Matrix.det_zero_of_row_eq hab
    rw [markedBirthEqualityMatrix_performed_row p a ha,
      markedBirthEqualityMatrix_performed_row p b hb, heq]

def MarkedBirthPermutationEvent {A P : Type*} (p : A → Option P) (σ : Equiv.Perm A) : Prop :=
  ∀ a, σ a = a ∨ p (σ a) ≠ none ∧ p (σ a) = p a

theorem markedBirthPermutationEvent_performed
    {A P : Type*} [Fintype A] [DecidableEq A] (p : A → Option P) (σ : Equiv.Perm A)
    (hσ : MarkedBirthPermutationEvent p σ) (a : A) (ha : a ∈ σ.support) : p a ≠ none := by
  obtain h | ⟨h,hp⟩ := hσ a
  · exact False.elim ((Equiv.Perm.mem_support.mp ha) h)
  · exact fun hz => h (hp.trans hz)

theorem markedBirthPermutationEvent_value
    {A P : Type*} (p : A → Option P) (σ : Equiv.Perm A)
    (hσ : MarkedBirthPermutationEvent p σ) (a : A) : p (σ a) = p a := by
  obtain h | h := hσ a
  · exact congrArg p h
  · exact h.2

theorem markedBirthPermutation_matrix_product
    {A P : Type*} [Fintype A] [DecidableEq A] (p : A → Option P) (σ : Equiv.Perm A) :
    (∏ a, markedBirthEqualityMatrix p (σ a) a) = if MarkedBirthPermutationEvent p σ then 1 else 0 := by
  by_cases hσ : MarkedBirthPermutationEvent p σ
  · rw [ite_eq_left hσ]
    apply Finset.prod_eq_one
    intro a _
    exact ite_eq_left (hσ a)
  · rw [ite_eq_right hσ]
    have hn : ∃ a, ¬(σ a = a ∨ p (σ a) ≠ none ∧ p (σ a) = p a) := not_forall.mp hσ
    obtain ⟨a,ha⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_univ a) (ite_eq_right ha)

theorem markedBirthDistinct_permutation_sum
    {A P : Type*} [Fintype A] [DecidableEq A] (p : A → Option P) :
    (if MarkedPerformedInjective p then (1 : ℤ) else 0) =
      ∑ σ : Equiv.Perm A, (σ.sign : ℤ) * (if MarkedBirthPermutationEvent p σ then 1 else 0) := by
  rw [← markedBirthEqualityMatrix_det p, Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  rw [markedBirthPermutation_matrix_product]
  simp only [Int.cast_id]

def markedBirthPermutationRank {A : Type*} [Fintype A] [DecidableEq A]
    (σ : Equiv.Perm A) : ℕ := σ.cycleType.sum - σ.cycleType.card

private theorem two_mul_card_le_sum (s : Multiset ℕ) (hs : ∀ n ∈ s, 2 ≤ n) : 2*s.card ≤ s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    have ha : 2 ≤ a := hs a (by simp)
    have hh := ih (fun n hn => hs n (by simp [hn]))
    simp only [Multiset.card_cons, Multiset.sum_cons]
    omega

theorem markedBirthPermutation_support_le_twice_rank
    {A : Type*} [Fintype A] [DecidableEq A] (σ : Equiv.Perm A) :
    σ.support.card ≤ 2*markedBirthPermutationRank σ := by
  have hc := two_mul_card_le_sum σ.cycleType (fun n hn => Equiv.Perm.two_le_of_mem_cycleType hn)
  rw [Equiv.Perm.sum_cycleType] at hc
  unfold markedBirthPermutationRank
  rw [Equiv.Perm.sum_cycleType]
  omega

theorem markedBirthPermutation_operations_le_twice_rank
    {A O : Type*} [Fintype A] [DecidableEq A] [DecidableEq O]
    (operation : A → O) (σ : Equiv.Perm A) :
    (σ.support.image operation).card ≤ 2*markedBirthPermutationRank σ :=
  (Finset.card_image_le).trans (markedBirthPermutation_support_le_twice_rank σ)

end ArtinMatthews
