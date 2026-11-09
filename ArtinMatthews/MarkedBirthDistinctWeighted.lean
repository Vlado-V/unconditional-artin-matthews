module

public import ArtinMatthews.MarkedBirthDistinctPermutation
public import Mathlib.Basic.Complex.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite interchange of the performed-birth inclusion-exclusion
with arbitrary complex history weights. No absolute-value estimate or
independence assumption is used in this algebraic identity. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedBirthDistinct_permutation_sum_complex
    {A P : Type*} [Fintype A] [DecidableEq A] (p : A → Option P) :
    (if MarkedPerformedInjective p then (1 : ℂ) else 0) =
      ∑ σ : Equiv.Perm A, ((σ.sign : ℤ) : ℂ) *
        (if MarkedBirthPermutationEvent p σ then 1 else 0) := by
  have h := congrArg (fun z : ℤ => (z : ℂ)) (markedBirthDistinct_permutation_sum p)
  simpa only [apply_ite, Int.cast_one, Int.cast_zero, Int.cast_sum, Int.cast_mul] using h

theorem markedBirthDistinct_weighted_permutation_sum
    {Ω A P : Type*} [Fintype Ω] [Fintype A] [DecidableEq A]
    (p : Ω → A → Option P) (F : Ω → ℂ) :
    (∑ x, if MarkedPerformedInjective (p x) then F x else 0) =
      ∑ σ : Equiv.Perm A, ((σ.sign : ℤ) : ℂ) *
        ∑ x, if MarkedBirthPermutationEvent (p x) σ then F x else 0 := by
  calc
    _ = ∑ x, (if MarkedPerformedInjective (p x) then (1 : ℂ) else 0)*F x := by
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp
    _ = ∑ x, ∑ σ : Equiv.Perm A, ((σ.sign : ℤ) : ℂ) *
        (if MarkedBirthPermutationEvent (p x) σ then F x else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [markedBirthDistinct_permutation_sum_complex, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro σ _
      split_ifs <;> simp
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro σ _
      rw [Finset.mul_sum]

end ArtinMatthews
