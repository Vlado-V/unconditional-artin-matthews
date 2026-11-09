module

public import ArtinMatthews.MarkedBirthDistinctPermutation


set_option backward.privateInPublic true
@[expose] public section

/-! One earliest address per nontrivial permutation cycle. The pivot
set is constructed from the actual disjoint cycle factors, and deleting
it from the moved addresses gives exactly the original permutation rank. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {A : Type*} [Fintype A] [DecidableEq A] [LinearOrder A] (σ : Equiv.Perm A)

def markedBirthCyclePivot (c : σ.cycleFactorsFinset) : A :=
  c.1.support.min' ((Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).1.nonempty_support)

theorem markedBirthCyclePivot_mem (c : σ.cycleFactorsFinset) :
    markedBirthCyclePivot σ c∈c.1.support :=
  Finset.min'_mem _ _

theorem markedBirthCyclePivot_le (c : σ.cycleFactorsFinset) (a : A) (ha : a∈c.1.support) :
    markedBirthCyclePivot σ c≤a := Finset.min'_le _ _ ha

theorem markedBirthCyclePivot_injective : Function.Injective (markedBirthCyclePivot σ) := by
  intro c d he
  by_contra hne
  have hcd : c.1≠d.1 := fun h => hne (Subtype.ext h)
  have hd := Equiv.Perm.Disjoint.disjoint_support
    (σ.cycleFactorsFinset_pairwise_disjoint c.2 d.2 hcd)
  apply Finset.disjoint_left.mp hd (markedBirthCyclePivot_mem σ c)
  rw [he]
  exact markedBirthCyclePivot_mem σ d

def markedBirthCyclePivots : Finset A := Finset.univ.image (markedBirthCyclePivot σ)

theorem markedBirthCyclePivots_subset : markedBirthCyclePivots σ⊆σ.support := by
  intro a ha
  obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp ha
  exact Equiv.Perm.mem_cycleFactorsFinset_support_le c.2 (markedBirthCyclePivot_mem σ c)

theorem markedBirthCyclePivots_card : (markedBirthCyclePivots σ).card=σ.cycleType.card := by
  unfold markedBirthCyclePivots
  rw [Finset.card_image_of_injective _ (markedBirthCyclePivot_injective σ),Finset.card_univ,Fintype.card_coe]
  simp only [Equiv.Perm.cycleType,Multiset.card_map,Finset.card]

def markedBirthCycleNonpivots : Finset A := σ.support \ markedBirthCyclePivots σ

theorem markedBirthCycleNonpivots_card :
    (markedBirthCycleNonpivots σ).card=markedBirthPermutationRank σ := by
  rw [markedBirthCycleNonpivots,Finset.card_sdiff_of_subset (markedBirthCyclePivots_subset σ),
    markedBirthCyclePivots_card,markedBirthPermutationRank,Equiv.Perm.sum_cycleType]

theorem markedBirthCycleNonpivots_support {a : A} (ha : a∈markedBirthCycleNonpivots σ) :
    a∈σ.support := (Finset.mem_sdiff.mp ha).1

end
end ArtinMatthews
