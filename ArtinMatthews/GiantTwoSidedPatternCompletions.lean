module

public import ArtinMatthews.GiantTwoSidedEndpointStates


set_option backward.privateInPublic true
@[expose] public section

/-! A pattern copies exactly the slots outside its actual free subset
among the first slots. Admissible completions inject into ordered
choices from the remaining active divisors. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev GiantTwoSidedPatternFreeSlots {k : ℕ} (C : Finset (Fin k)) (ell : ℕ) :=
  ↥C ⊕ Fin ell

def giantTwoSidedPatternFreeSlot {k : ℕ} (C : Finset (Fin k)) (ell : ℕ) :
    GiantTwoSidedPatternFreeSlots C ell → Fin (k+ell) :=
  Sum.elim (fun i => Fin.castAdd ell i.val) (Fin.natAdd k)

def giantTwoSidedPatternCopiedValues (P : Finset ℕ) {k ell : ℕ} (C : Finset (Fin k))
    (a : Fin (k+ell) → ↥P) : Finset ℕ :=
  (univ \ C).image (fun i => (a (Fin.castAdd ell i):ℕ))

abbrev GiantTwoSidedPatternCompletion (P : Finset ℕ) {k ell : ℕ} (C : Finset (Fin k))
    (n : ℕ) (a : Fin (k+ell) → ↥P) :=
  {b : Fin (k+ell) → ↥P // Function.Injective b ∧ (∀ i,(b i:ℕ) ∣ n) ∧
    ∀ i : Fin k,i∉C → b (Fin.castAdd ell i)=a (Fin.castAdd ell i)}

theorem giantTwoSidedPatternCompletion_count_le (P : Finset ℕ) {k ell : ℕ}
    (C : Finset (Fin k)) {n : ℕ} {a : Fin (k+ell) → ↥P}
    (b : GiantTwoSidedPatternCompletion P C n a) : k+ell ≤ bandCount P n := by
  let f (i : Fin (k+ell)) : ↥(activeDivisors P n) :=
    ⟨(b.val i:ℕ),mem_filter.mpr ⟨(b.val i).property,b.property.2.1 i⟩⟩
  have hf : Function.Injective f := fun _ _ h => b.property.1 (Subtype.ext
    (congrArg (fun a : ↥(activeDivisors P n) => a.val) h))
  simpa only [Fintype.card_fin,Fintype.card_coe,bandCount] using Fintype.card_le_of_injective f hf

theorem giantTwoSidedPatternCompletion_card_le (P : Finset ℕ) {k ell : ℕ}
    (C : Finset (Fin k)) (n : ℕ) (a : Fin (k+ell) → ↥P) (ha : Function.Injective a) :
    Fintype.card (GiantTwoSidedPatternCompletion P C n a) ≤
      (bandCount P n-(k+ell)+(ell+C.card))^(ell+C.card) := by
  classical
  by_cases h : Nonempty (GiantTwoSidedPatternCompletion P C n a)
  · obtain ⟨b₀⟩ := h
    let copied := giantTwoSidedPatternCopiedValues P C a
    let fresh := activeDivisors P n \ copied
    have hc : copied ⊆ activeDivisors P n := by
      intro p hp
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
      rw [← b₀.property.2.2 i (mem_sdiff.mp hi).2]
      exact mem_filter.mpr ⟨(b₀.val (Fin.castAdd ell i)).property,b₀.property.2.1 _⟩
    have hcopied : copied.card=k-C.card := by
      unfold copied giantTwoSidedPatternCopiedValues
      have hi : Function.Injective (fun i : Fin k => (a (Fin.castAdd ell i):ℕ)) :=
        Subtype.val_injective.comp (ha.comp (Fin.castAdd_injective k ell))
      rw [card_image_of_injective _ hi,card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin]
    have hC : C.card≤k := by simpa only [card_univ,Fintype.card_fin] using card_le_card (subset_univ C)
    have hfresh : fresh.card = bandCount P n-(k+ell)+(ell+C.card) := by
      unfold fresh
      rw [card_sdiff_of_subset hc,hcopied,← bandCount]
      have hcount := giantTwoSidedPatternCompletion_count_le P C b₀
      omega
    let f (b : GiantTwoSidedPatternCompletion P C n a)
        (s : GiantTwoSidedPatternFreeSlots C ell) : ↥fresh := by
      let l := giantTwoSidedPatternFreeSlot C ell s
      refine ⟨(b.val l:ℕ),mem_sdiff.mpr ⟨mem_filter.mpr ⟨(b.val l).property,b.property.2.1 l⟩,?_⟩⟩
      intro hl
      obtain ⟨i,hi,he⟩ := mem_image.mp hl
      have hiC : i∉C := (mem_sdiff.mp hi).2
      have hli : Fin.castAdd ell i=l := b.property.1 (Subtype.ext
        ((congrArg Subtype.val (b.property.2.2 i hiC)).trans he))
      cases s with
      | inl s =>
        change Fin.castAdd ell i=Fin.castAdd ell s.val at hli
        exact hiC (Fin.castAdd_injective k ell hli ▸ s.property)
      | inr s =>
        have hh := congrArg Fin.val hli
        change i.val=k+s.val at hh
        omega
    have hf : Function.Injective f := by
      intro b b' hb
      apply Subtype.ext
      funext i
      refine Fin.addCases (m:=k) (n:=ell) ?_ ?_ i
      · intro l
        by_cases hl : l∈C
        · exact Subtype.ext (congrArg (fun p : ↥fresh => p.val) (congrFun hb (Sum.inl ⟨l,hl⟩)))
        · exact (b.property.2.2 l hl).trans (b'.property.2.2 l hl).symm
      · intro l
        exact Subtype.ext (congrArg (fun p : ↥fresh => p.val) (congrFun hb (Sum.inr l)))
    calc
      _ ≤ Fintype.card (GiantTwoSidedPatternFreeSlots C ell → ↥fresh) := Fintype.card_le_of_injective f hf
      _ = _ := by rw [Fintype.card_fun,Fintype.card_coe,hfresh,Fintype.card_sum,
        Fintype.card_coe,Fintype.card_fin,Nat.add_comm C.card ell]
  · rw [Fintype.card_eq_zero_iff.mpr (not_nonempty_iff.mp h)]
    exact Nat.zero_le _

end
end ArtinMatthews
