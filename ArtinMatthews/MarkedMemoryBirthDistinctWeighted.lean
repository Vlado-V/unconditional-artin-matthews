module

public import ArtinMatthews.MarkedMemoryPotentialDistinct
public import ArtinMatthews.MarkedBirthDistinctWeighted
public import ArtinMatthews.MarkedBirthRankCount


set_option backward.privateInPublic true
@[expose] public section

/-! The fixed-address inclusion-exclusion applied to the original finite
chronological histories. The weight is arbitrary: all actual coefficients,
cutoffs and boundary factors may remain inside it. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

local instance potentialPermFintype
    {J : Type*} [Fintype J] [DecidableEq J] (M B n : ℕ) :
    Fintype (Equiv.Perm (MarkedMemoryPotentialAddress J M B n)) :=
  @Equiv.instFintype (MarkedMemoryPotentialAddress J M B n)
    (MarkedMemoryPotentialAddress J M B n) inferInstance inferInstance inferInstance inferInstance

theorem markedMemoryHistoryBirthDistinct_weighted_permutation_sum
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (s : MarkedRawState P (pads+1) B Z)
    (F : MarkedMemoryChronologicalHistory hZ n s → ℂ) :
    (∑ h, if MarkedMemoryHistoryBirthDistinct hZ h then F h else 0) =
      ∑ σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B n),
        ((σ.sign : ℤ) : ℂ) *
          ∑ h, if MarkedBirthPermutationEvent (markedMemoryPotentialAddressValue hZ h) σ
            then F h else 0 := by
  simp_rw [markedMemoryHistoryBirthDistinct_iff_potential]
  exact markedBirthDistinct_weighted_permutation_sum
    (fun h : MarkedMemoryChronologicalHistory hZ n s => markedMemoryPotentialAddressValue hZ h) F

theorem markedMemoryHistoryBirthDistinct_boundary_permutation_sum
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (F : (s : MarkedRawState P (pads+1) B Z) → MarkedMemoryChronologicalHistory hZ n s → ℂ) :
    (∑ s, ∑ h, if MarkedMemoryHistoryBirthDistinct hZ h then F s h else 0) =
      ∑ σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B n),
        ((σ.sign : ℤ) : ℂ) *
          ∑ s, ∑ h, if MarkedBirthPermutationEvent (markedMemoryPotentialAddressValue hZ h) σ
            then F s h else 0 := by
  simp_rw [markedMemoryHistoryBirthDistinct_weighted_permutation_sum hZ]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.mul_sum]

theorem markedMemoryBirth_rank_operation_bound
    {J : Type*} [Fintype J] [DecidableEq J] (M B n : ℕ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B n)) :
    (σ.support.image markedMemoryPotentialOperation).card ≤ 2*markedBirthPermutationRank σ :=
  markedBirthPermutation_operations_le_twice_rank markedMemoryPotentialOperation σ

theorem markedMemoryBirth_rank_coefficient_bound
    {J : Type*} [Fintype J] [DecidableEq J] (M B n r : ℕ) :
    Fintype.card {σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B n) //
      markedBirthPermutationRank σ = r} ≤
        ((Fintype.card J*M+(n+1)*Fintype.card J*B+n*Fintype.card J)^2+1)^(2*r) := by
  have h := markedBirthPermutation_rank_card_bound
    (A := MarkedMemoryPotentialAddress J M B n) r
  simpa only [markedMemoryPotentialAddress_card, pow_two] using h

end ArtinMatthews
