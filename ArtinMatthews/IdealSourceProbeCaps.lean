module

public import ArtinMatthews.IdealSourceBlocks
public import ArtinMatthews.IdealResidualFamily


set_option backward.privateInPublic true
@[expose] public section

/-! Every actual selected comparison frees at most the designated
first-m slots per group and frees no coordinates outside its blocks. -/
namespace ArtinMatthews
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealSourceProbes_union {G : Type*} [DecidableEq G] (S T : Finset G)
    {m J : ℕ} (hm : m ≤ J) :
    idealSourceProbes S hm ∪ idealSourceProbes T hm = idealSourceProbes (S ∪ T) hm := by
  ext v
  rcases v with ⟨g,i⟩
  simp only [mem_union, idealSourceProbes_mem]
  tauto

theorem idealSource_freeSlots_subset {G : Type*} [DecidableEq G]
    (S : Finset G) {m J : ℕ} (hm : m ≤ J) (A : Finset (G × Fin J))
    (hA : A ⊆ idealSourceProbes S hm) (g : G) :
    idealResidualFreeSlots A g ⊆ idealSourceFirstSlots hm := by
  intro i hi
  have h := (idealSourceProbes_mem S hm g i).mp (hA ((mem_idealResidualFreeSlots A g i).mp hi))
  exact (idealSourceFirstSlots_mem hm i).mpr h.2

theorem idealSource_freeSlots_card_le {G : Type*} [DecidableEq G]
    (S : Finset G) {m J : ℕ} (hm : m ≤ J) (A : Finset (G × Fin J))
    (hA : A ⊆ idealSourceProbes S hm) (g : G) :
    (idealResidualFreeSlots A g).card ≤ m :=
  (card_le_card (idealSource_freeSlots_subset S hm A hA g)).trans_eq (idealSourceFirstSlots_card hm)

theorem idealSource_freeSlots_eq_empty {G : Type*} [DecidableEq G]
    (S : Finset G) {m J : ℕ} (hm : m ≤ J) (A : Finset (G × Fin J))
    (hA : A ⊆ idealSourceProbes S hm) (g : G) (hg : g ∉ S) :
    idealResidualFreeSlots A g = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro i hi
  exact hg ((idealSourceProbes_mem S hm g i).mp (hA ((mem_idealResidualFreeSlots A g i).mp hi))).1

theorem idealSourceResidualCopied_card_le {G : Type*} [DecidableEq G]
    (S T : Finset G) {m J : ℕ} (hm : m ≤ J) (ν : IdealResidualPattern G J)
    (hν : ν ∈ idealResidualPatterns (idealSourceProbes S hm) (idealSourceProbes T hm)) (g : G) :
    (idealResidualCopied ν g).card ≤ m := by
  cases ν with
  | none => exact Nat.zero_le m
  | some v =>
    rcases v with ⟨A,B⟩
    have h := (idealResidualPatterns_comparison (idealSourceProbes S hm) (idealSourceProbes T hm) A B).mp hν
    have hA : A ⊆ idealSourceProbes S hm := mem_powerset.mp (mem_of_mem_erase h.1)
    have hB : B ⊆ idealSourceProbes T hm := mem_powerset.mp (mem_of_mem_erase h.2)
    apply idealSource_freeSlots_card_le (S ∪ T) hm (A ∪ B) _ g
    rw [← idealSourceProbes_union S T hm]
    exact union_subset_union hA hB

theorem idealSourceResidualCopied_outside {G : Type*} [DecidableEq G]
    (S T : Finset G) {m J : ℕ} (hm : m ≤ J) (ν : IdealResidualPattern G J)
    (hν : ν ∈ idealResidualPatterns (idealSourceProbes S hm) (idealSourceProbes T hm))
    (g : G) (hg : g ∉ S ∪ T) : idealResidualCopied ν g = ∅ := by
  cases ν with
  | none => rfl
  | some v =>
    rcases v with ⟨A,B⟩
    have h := (idealResidualPatterns_comparison (idealSourceProbes S hm) (idealSourceProbes T hm) A B).mp hν
    have hA : A ⊆ idealSourceProbes S hm := mem_powerset.mp (mem_of_mem_erase h.1)
    have hB : B ⊆ idealSourceProbes T hm := mem_powerset.mp (mem_of_mem_erase h.2)
    apply idealSource_freeSlots_eq_empty (S ∪ T) hm (A ∪ B) _ g hg
    rw [← idealSourceProbes_union S T hm]
    exact union_subset_union hA hB

end
end ArtinMatthews
