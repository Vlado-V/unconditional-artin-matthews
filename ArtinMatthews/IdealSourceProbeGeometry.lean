module

public import ArtinMatthews.IdealSourceBlocks
public import ArtinMatthews.IdealFirstCoordinates


set_option backward.privateInPublic true
@[expose] public section

/-! Canonical source probes and the literal last-slot average satisfy
the full-coordinate hypotheses of the symmetric survivor estimate. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def idealSourceFullProbeSlots {m J : ℕ} (hm : m ≤ J) (ell : ℕ) : Finset (Fin (J+ell)) :=
  (idealSourceFirstSlots hm).map (Fin.castAddEmb ell)

def idealSourceTailSlots (J ell : ℕ) : Finset (Fin (J+ell)) :=
  (univ : Finset (Fin ell)).map (Fin.natAddEmb J)

theorem idealSourceFullProbeSlots_card {m J : ℕ} (hm : m ≤ J) (ell : ℕ) :
    (idealSourceFullProbeSlots hm ell).card = m := by
  rw [idealSourceFullProbeSlots, card_map, idealSourceFirstSlots_card]

theorem idealSourceTailSlots_card (J ell : ℕ) : (idealSourceTailSlots J ell).card = ell := by
  simp only [idealSourceTailSlots, card_map, card_univ, Fintype.card_fin]

theorem idealSourceFullProbeSlots_disjoint {m J : ℕ} (hm : m ≤ J) (ell : ℕ) :
    Disjoint (idealSourceFullProbeSlots hm ell) (idealSourceTailSlots J ell) := by
  apply disjoint_left.mpr
  intro v hp ht
  obtain ⟨i, _, hi⟩ := mem_map.mp hp
  obtain ⟨j, _, hj⟩ := mem_map.mp ht
  have hpi := congrArg Fin.val hi
  have htj := congrArg Fin.val hj
  change i.val = v.val at hpi
  change J+j.val = v.val at htj
  have hib := i.isLt
  omega

theorem idealSourceFullProbeSlots_included {G : Type*} (S : Finset G)
    {m J : ℕ} (hm : m ≤ J) (ell : ℕ) (g : G) (hg : g ∈ S)
    (i : Fin (J+ell)) (hi : i ∈ idealSourceFullProbeSlots hm ell) :
    (g,i) ∈ idealFirstCoordinates ell (idealSourceProbes S hm) := by
  obtain ⟨j, hj, rfl⟩ := mem_map.mp hi
  apply mem_map.mpr
  refine ⟨(g,j), mem_product.mpr ⟨hg,hj⟩, ?_⟩
  rfl

theorem idealSourceTailSlots_included {G : Type*} [Fintype G] [DecidableEq G]
    (J ell : ℕ) (g : G) (i : Fin (J+ell)) (hi : i ∈ idealSourceTailSlots J ell) :
    (g,i) ∈ idealPatternFreeCoordinates (ell := ell) (fun _ : G => (∅ : Finset (Fin J))) := by
  obtain ⟨j, _, rfl⟩ := mem_map.mp hi
  exact idealPatternFreeCoordinates_tail (fun _ : G => (∅ : Finset (Fin J))) g j

end
end ArtinMatthews
