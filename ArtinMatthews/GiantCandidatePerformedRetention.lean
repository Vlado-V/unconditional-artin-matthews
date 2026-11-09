module

public import ArtinMatthews.GiantSignedJoinedSourceFamily
public import ArtinMatthews.GiantCandidateCoinSets


set_option backward.privateInPublic true
@[expose] public section

/-! Retention counts the actual selected small and big carriers. The
same positive retained threshold is available before the residual family. -/
namespace ArtinMatthews
open Finset
noncomputable section

theorem giantCandidatePerformedSmall_card {x : ℝ} (groups : Finset (GiantCandidateGroupIndex x)) :
    Fintype.card (GiantCandidatePerformedSmall groups) = (groups ∩ giantCandidateCoinSmall x).card := by
  let e : GiantCandidatePerformedSmall groups ↪ GiantCandidateGroupIndex x :=
    ⟨fun i => .inl i.val, Sum.inl_injective.comp Subtype.val_injective⟩
  have h : univ.map e = groups ∩ giantCandidateCoinSmall x := by
    ext a
    constructor
    · intro ha
      obtain ⟨i,_,rfl⟩ := mem_map.mp ha
      exact mem_inter.mpr ⟨i.property,mem_map.mpr ⟨i.val,mem_univ _,rfl⟩⟩
    · intro ha
      obtain ⟨hg,hs⟩ := mem_inter.mp ha
      obtain ⟨i,_,rfl⟩ := mem_map.mp hs
      exact mem_map.mpr ⟨⟨i,hg⟩,mem_univ _,rfl⟩
  rw [← h,card_map,card_univ]

theorem giantCandidatePerformedBig_card {x : ℝ} (groups : Finset (GiantCandidateGroupIndex x)) :
    Fintype.card (GiantCandidatePerformedBig groups) = (groups ∩ giantCandidateCoinBig x).card := by
  let e : GiantCandidatePerformedBig groups ↪ GiantCandidateGroupIndex x :=
    ⟨fun i => .inr i.val, Sum.inr_injective.comp Subtype.val_injective⟩
  have h : univ.map e = groups ∩ giantCandidateCoinBig x := by
    ext a
    constructor
    · intro ha
      obtain ⟨i,_,rfl⟩ := mem_map.mp ha
      exact mem_inter.mpr ⟨i.property,mem_map.mpr ⟨i.val,mem_univ _,rfl⟩⟩
    · intro ha
      obtain ⟨hg,hs⟩ := mem_inter.mp ha
      obtain ⟨i,_,rfl⟩ := mem_map.mp hs
      exact mem_map.mpr ⟨⟨i,hg⟩,mem_univ _,rfl⟩
  rw [← h,card_map,card_univ]

theorem giantCandidatePerformed_retained_iff {x threshold : ℝ} (groups : Finset (GiantCandidateGroupIndex x)) :
    groups ∈ giantCandidateRetainedOutcomes x threshold ↔
      threshold*Real.log (Real.log x) ≤ (Fintype.card (GiantCandidatePerformedSmall groups) : ℝ) ∧
      threshold*Real.log (Real.log x) ≤ (Fintype.card (GiantCandidatePerformedBig groups) : ℝ) := by
  rw [giantCandidatePerformedSmall_card,giantCandidatePerformedBig_card,mem_giantCandidateRetainedOutcomes]

end
end ArtinMatthews
