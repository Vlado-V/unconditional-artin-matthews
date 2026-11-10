module

public import Mathlib.Basic.Real.Basic
public import ArtinMatthews.MarkedBirthDistinctPermutation
public import ArtinMatthews.MarkedBirthRankCount


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite grouping of the signed-permutation expansion by cycle
rank, followed by the proved coefficient-count bound. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedBirthRankSliceEquiv {A : Type*} [Fintype A] [DecidableEq A] (r₀ : ℕ) :
    {σ : Equiv.Perm A // markedBirthPermutationRank σ < r₀} ≃
      Σ r : Fin r₀, {σ : Equiv.Perm A // markedBirthPermutationRank σ = r.1} where
  toFun σ := ⟨⟨markedBirthPermutationRank σ.1,σ.2⟩,⟨σ.1,rfl⟩⟩
  invFun x := ⟨x.2.1,by rw [x.2.2]; exact x.1.2⟩
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨⟨r,hr⟩,σ,hσ⟩
    dsimp only at hσ
    subst r
    rfl

theorem markedBirthRank_low_sum_eq {A : Type*} [Fintype A] [DecidableEq A]
    (r₀ : ℕ) (F : Equiv.Perm A → ℝ) :
    (∑ σ, if markedBirthPermutationRank σ < r₀ then F σ else 0) =
      ∑ r ∈ Finset.range r₀, ∑ σ : {σ : Equiv.Perm A // markedBirthPermutationRank σ = r}, F σ.1 := by
  classical
  have he := Equiv.sum_comp (markedBirthRankSliceEquiv (A := A) r₀) (fun x => F x.2.1)
  have hs : (∑ σ, if markedBirthPermutationRank σ < r₀ then F σ else 0) =
      ∑ σ : {σ : Equiv.Perm A // markedBirthPermutationRank σ < r₀}, F σ.1 := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype (p := fun σ : Equiv.Perm A => markedBirthPermutationRank σ < r₀)
      (Finset.univ.filter (fun σ : Equiv.Perm A => markedBirthPermutationRank σ < r₀))
      (by intro σ; simp only [Finset.mem_filter,Finset.mem_univ,true_and]) F
  rw [hs]
  calc
    _ = ∑ r : Fin r₀, ∑ σ : {σ : Equiv.Perm A // markedBirthPermutationRank σ = r.1}, F σ.1 := by
      simpa only [Fintype.sum_sigma,markedBirthRankSliceEquiv,Equiv.coe_fn_mk] using he
    _ = _ := Fin.sum_univ_eq_sum_range (fun r => ∑ σ : {σ : Equiv.Perm A // markedBirthPermutationRank σ = r}, F σ.1) r₀

theorem markedBirthRank_low_sum_le {A : Type*} [Fintype A] [DecidableEq A]
    (r₀ : ℕ) (F : Equiv.Perm A → ℝ) (T : ℕ → ℝ)
    (hT : ∀ r < r₀, 0 ≤ T r)
    (hF : ∀ σ, markedBirthPermutationRank σ < r₀ → F σ ≤ T (markedBirthPermutationRank σ)) :
    (∑ σ, if markedBirthPermutationRank σ < r₀ then F σ else 0) ≤
      ∑ r ∈ Finset.range r₀, ((Fintype.card A:ℝ)^2+1)^(2*r)*T r := by
  rw [markedBirthRank_low_sum_eq]
  apply Finset.sum_le_sum
  intro r hr
  have hrr : r < r₀ := Finset.mem_range.mp hr
  have hcard : (Fintype.card {σ : Equiv.Perm A // markedBirthPermutationRank σ = r}:ℝ) ≤
      ((Fintype.card A:ℝ)^2+1)^(2*r) := by
    have h := markedBirthPermutation_rank_card_bound (A := A) r
    rw [pow_two]
    exact_mod_cast h
  calc
    _ ≤ ∑ _σ : {σ : Equiv.Perm A // markedBirthPermutationRank σ = r}, T r := by
      apply Finset.sum_le_sum
      intro σ _
      have hh := hF σ.1 (by rw [σ.2]; exact hrr)
      simpa only [σ.2] using hh
    _ = (Fintype.card {σ : Equiv.Perm A // markedBirthPermutationRank σ = r}:ℝ)*T r := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (hT r hrr)

end ArtinMatthews
