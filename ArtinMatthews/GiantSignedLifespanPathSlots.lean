module

public import ArtinMatthews.GiantSignedEdgeStorePromote
public import ArtinMatthews.GiantTwoSidedResiduePathArithmetic


set_option backward.privateInPublic true
@[expose] public section

/-! The ordered free slots in the original label path are exactly its
departing and newly active primes. These are the slots that can store or
retrieve a particle in the chronological reconstruction. -/

namespace ArtinMatthews
open Finset
noncomputable section

theorem giantTwoSidedPatternFreeSlot_injective {k ell : ℕ} (C : Finset (Fin k)) :
    Function.Injective (giantTwoSidedPatternFreeSlot C ell) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      exact congrArg Sum.inl (Subtype.ext (Fin.castAdd_injective k ell h))
    | inr b =>
      have hv := congrArg Fin.val h
      change a.val.val = k + b.val at hv
      omega
  | inr a =>
    cases b with
    | inl b =>
      have hv := congrArg Fin.val h
      change k + a.val = b.val.val at hv
      omega
    | inr b =>
      have hv := congrArg Fin.val h
      change k + a.val = k + b.val at hv
      exact congrArg Sum.inr (Fin.ext (Nat.add_left_cancel hv))

theorem giantSignedPatternFreeLabels_injective {J : Type*} {P : J → Finset ℕ} {k ell : ℕ}
    (C : J → Finset (Fin k)) (a : MarkedPhysicalMarking P (k+ell))
    (ha : MarkedPhysicalMarkingDistinct a) (g : J) :
    Function.Injective (giantSignedPatternFreeLabels C a g) :=
  (ha g).comp ((giantTwoSidedPatternFreeSlot_injective (C g)).comp
    (giantSignedPatternFreeSlotEquiv (C g) ell).injective)

private theorem freeSlot_range_iff {P : Finset ℕ} {k ell : ℕ} (C : Finset (Fin k))
    (a b : Fin (k+ell) → P) (ha : Function.Injective a)
    (hcopy : ∀ i : Fin k, i ∉ C → a (Fin.castAdd ell i) = b (Fin.castAdd ell i))
    (hcommon : ∀ p : P, (∃ j, a j = p) → (∃ j, b j = p) →
      ∃ l : Fin k, l ∉ C ∧ a (Fin.castAdd ell l) = p)
    (p : P) :
    (∃ j : Fin (ell+C.card), a (giantTwoSidedPatternFreeSlot C ell
        (giantSignedPatternFreeSlotEquiv C ell j)) = p) ↔
      (∃ j, a j = p) ∧ ¬(∃ j, b j = p) := by
  constructor
  · rintro ⟨j, hj⟩
    let u := giantSignedPatternFreeSlotEquiv C ell j
    have hocc : ∃ j, a j = p := ⟨_, hj⟩
    refine ⟨hocc, fun ht => ?_⟩
    obtain ⟨l,hl,he⟩ := hcommon p hocc ht
    exact giantTwoSidedPatternFreeSlot_not_copiedValue P C a ha u
      (mem_image.mpr ⟨l,mem_sdiff.mpr ⟨mem_univ _,hl⟩,congrArg Subtype.val (he.trans hj.symm)⟩)
  · rintro ⟨⟨j,hj⟩, hnot⟩
    revert hj
    refine Fin.addCases ?_ ?_ j
    · intro l hl
      have hC : l ∈ C := by
        by_contra hh
        exact hnot ⟨Fin.castAdd ell l,(hcopy l hh).symm.trans hl⟩
      obtain ⟨z,hz⟩ := (giantSignedPatternFreeSlotEquiv C ell).surjective (.inl ⟨l,hC⟩)
      exact ⟨z, by rw [hz]; exact hl⟩
    · intro l hl
      obtain ⟨z,hz⟩ := (giantSignedPatternFreeSlotEquiv C ell).surjective (.inr l)
      exact ⟨z, by rw [hz]; exact hl⟩

variable {J : Type*} [Fintype J] {P : J → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → J → Finset (Fin k)} {labels : Fin (n+1) → MarkedPhysicalMarking P (k+ell)}
    {π τ : Fin n → J → Equiv.Perm (Fin (k+ell))}
    {aux : ∀ i, GiantTwoSidedPatternAuxiliary P (C i)} {step : Fin n → ℤ}

theorem giantSignedActiveVisits_iff_group_slot
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (labels : Fin (n+1) → MarkedPhysicalMarking P (k+ell)) (v : Fin (n+1)) (g : J) (p : P g) :
    v ∈ giantSignedActualActiveVisits labels p.val ↔ ∃ l, labels v g l = p := by
  rw [mem_giantSignedActualActiveVisits]
  constructor
  · rintro ⟨j,l,hl⟩
    have hj : j = g := by
      by_contra hh
      exact (Finset.disjoint_left.mp (hdis hh)) (hl ▸ (labels v j l).property) p.property
    subst j
    exact ⟨l,Subtype.ext hl⟩
  · rintro ⟨l,rfl⟩
    exact ⟨g,l,rfl⟩

theorem giantSignedLifespanPath_free_slots
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hstep : ∀ i, 0 < (step i).natAbs) (hsize : ∀ i j p, p ∈ P j → (step i).natAbs < p)
    (hguard : GiantTwoSidedStaticLabels C π τ aux labels)
    (hcompat : GiantTwoSidedActiveCompatible univ labels
      (giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C labels π aux step)))
    (i : Fin n) (g : J) (p : P g) :
    let A := giantSignedActualActiveVisits labels p.val
    let source := giantTwoSidedPermuteLabels (π i) (labels i.castSucc)
    let target := giantTwoSidedPermuteLabels (τ i) (labels i.succ)
    ((∃ j, giantSignedPatternFreeLabels (C i) source g j = p) ↔ i.castSucc ∈ A ∧ i.succ ∉ A) ∧
      ((∃ j, giantSignedPatternFreeLabels (C i) target g j = p) ↔ i.succ ∈ A ∧ i.castSucc ∉ A) := by
  let a := giantTwoSidedPermuteLabels (π i) (labels i.castSucc) g
  let b := giantTwoSidedPermuteLabels (τ i) (labels i.succ) g
  have ha (p : P g) : (∃ l, a l = p) ↔ i.castSucc ∈ giantSignedActualActiveVisits labels p.val := by
    rw [giantSignedActiveVisits_iff_group_slot hdis labels i.castSucc g p]
    constructor
    · rintro ⟨l,hl⟩
      exact ⟨π i g l, hl⟩
    · rintro ⟨l,hl⟩
      refine ⟨(π i g).symm l, ?_⟩
      simpa only [a,giantTwoSidedPermuteLabels,Equiv.apply_symm_apply] using hl
  have hb (p : P g) : (∃ l, b l = p) ↔ i.succ ∈ giantSignedActualActiveVisits labels p.val := by
    rw [giantSignedActiveVisits_iff_group_slot hdis labels i.succ g p]
    constructor
    · rintro ⟨l,hl⟩
      exact ⟨τ i g l, hl⟩
    · rintro ⟨l,hl⟩
      refine ⟨(τ i g).symm l, ?_⟩
      simpa only [b,giantTwoSidedPermuteLabels,Equiv.apply_symm_apply] using hl
  have hcopy (l : Fin k) (hl : l ∉ C i g) : a (Fin.castAdd ell l) = b (Fin.castAdd ell l) :=
    ((hguard.2 i).copied g l hl).symm
  have hcommon (p : P g) (hs : ∃ l, a l = p) (ht : ∃ l, b l = p) :
      ∃ l : Fin k, l ∉ C i g ∧ a (Fin.castAdd ell l) = p ∧ b (Fin.castAdd ell l) = p := by
    obtain ⟨l,hl,hl1,hl2⟩ :=
      (giantTwoSidedIndependentPath_adjacent_active_iff_sharedSlot hP hdis hstep hsize hguard hcompat
        i g p.property).mp ⟨(ha p).mp hs,(hb p).mp ht⟩
    exact ⟨l,hl,Subtype.ext hl1,Subtype.ext hl2⟩
  refine ⟨?_,?_⟩
  · change (∃ j, a (giantTwoSidedPatternFreeSlot (C i g) ell
        (giantSignedPatternFreeSlotEquiv (C i g) ell j)) = p) ↔ _
    simpa only [ha,hb] using freeSlot_range_iff (C i g) a b
      ((hguard.1 i.castSucc g).comp (π i g).injective) hcopy
      (fun p hs ht => let ⟨l,hl,h₁,_⟩ := hcommon p hs ht; ⟨l,hl,h₁⟩) p
  · change (∃ j, b (giantTwoSidedPatternFreeSlot (C i g) ell
        (giantSignedPatternFreeSlotEquiv (C i g) ell j)) = p) ↔ _
    simpa only [ha,hb] using freeSlot_range_iff (C i g) b a
      ((hguard.1 i.succ g).comp (τ i g).injective) (fun l hl => (hcopy l hl).symm)
      (fun p ht hs => let ⟨l,hl,_,h₂⟩ := hcommon p hs ht; ⟨l,hl,h₂⟩) p

end
end ArtinMatthews
