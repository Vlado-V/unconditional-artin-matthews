module

public import ArtinMatthews.GiantSignedChronologicalLifeEndpoints
public import ArtinMatthews.GiantSignedChronologicalAnchorHits


set_option backward.privateInPublic true
@[expose] public section

/-! Before and after pending statuses are the literal half-open
intervals, with the same residue anchor at the actual birth visit. -/

namespace ArtinMatthews
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}
    {h : GiantSignedChronologicalChoices PS PB ell C batch} {g : B} {p : PB g}

namespace GiantSignedChronologicalLifeEndpoints

variable (L : GiantSignedChronologicalLifeEndpoints h g p)
    (κ : Fin n → ℤ) (ha : GiantSignedChronologicalAdmissible κ h)
    (hd : GiantSignedBirthDistinct (giantSignedChronologicalBirthData h))

include ha hd in
theorem pendingBefore_iff (i : Fin (n+1)) :
    GiantSignedChronologicalPendingBefore h i g p ↔
      L.start < i ∧ i ≤ L.finish ∧ ¬GiantSignedChronologicalActive h i g p := by
  constructor
  · intro hp
    have hn := giantSignedChronologicalPendingBefore_not_active h κ ha hd i g p hp
    have ht := (L.live _).mp ((giantSignedChronologicalLiveAt_before_iff h i g p).mpr (Or.inr hp))
    change L.startTime ≤ 2*i.val ∧ 2*i.val ≤ L.endTime at ht
    have hle : L.start ≤ i := by change L.start.val ≤ i.val; rw [L.start_val]; omega
    have hlt : L.start < i := lt_of_le_of_ne hle (fun he => by
      have ho := L.start_inactive_iff.mp (fun hh => hn (he ▸ hh))
      have hval := congrArg Fin.val he
      rw [L.start_val] at hval
      omega)
    exact ⟨hlt,by change i.val ≤ L.finish.val; rw [L.finish_val]; omega,hn⟩
  · rintro ⟨hs,hf,hn⟩
    have ht : L.startTime ≤ 2*i.val ∧ 2*i.val ≤ L.endTime := by
      change L.start.val < i.val at hs
      change i.val ≤ L.finish.val at hf
      rw [L.start_val] at hs
      rw [L.finish_val] at hf
      omega
    exact ((giantSignedChronologicalLiveAt_before_iff h i g p).mp ((L.live _).mpr ht)).resolve_left hn

include ha hd in
theorem pendingAfter_iff (i : Fin (n+1)) :
    GiantSignedChronologicalPendingAfter h i g p ↔
      L.start ≤ i ∧ i < L.finish ∧ ¬GiantSignedChronologicalActive h i g p := by
  constructor
  · intro hp
    have hn := giantSignedChronologicalPendingAfter_not_active h κ ha hd i g p hp
    have ht := (L.live _).mp ((giantSignedChronologicalLiveAt_after_iff h i g p).mpr (Or.inr hp))
    change L.startTime ≤ 2*i.val+1 ∧ 2*i.val+1 ≤ L.endTime at ht
    have hle : i ≤ L.finish := by change i.val ≤ L.finish.val; rw [L.finish_val]; omega
    have hlt : i < L.finish := lt_of_le_of_ne hle (fun he => by
      have heven := (L.finish_inactive_iff κ ha).mp (fun hh => hn (he.symm ▸ hh))
      have hval := congrArg Fin.val he
      rw [L.finish_val] at hval
      omega)
    exact ⟨by change L.start.val ≤ i.val; rw [L.start_val]; omega,hlt,hn⟩
  · rintro ⟨hs,hf,hn⟩
    have ht : L.startTime ≤ 2*i.val+1 ∧ 2*i.val+1 ≤ L.endTime := by
      change L.start.val ≤ i.val at hs
      change i.val < L.finish.val at hf
      rw [L.start_val] at hs
      rw [L.finish_val] at hf
      omega
    exact ((giantSignedChronologicalLiveAt_after_iff h i g p).mp ((L.live _).mpr ht)).resolve_left hn

theorem birthOffset_eq (offset : Fin (n+1) → ℤ) :
    giantSignedBirthOffset offset (giantSignedChronologicalBirthData h) L.birth = offset L.start := by
  have hstart : L.start.val =
      giantSignedPerformedBirthTime (giantSignedChronologicalBirthData h) L.birth / 2 := rfl
  rcases hb : L.birth with a | (a | a)
  · have he : L.start = 0 := Fin.ext (by
      rw [hstart,hb]
      simp only [giantSignedPerformedBirthTime,Nat.zero_div,Fin.val_zero])
    exact congrArg offset he.symm
  · have he : L.start = a.1.succ := Fin.ext (by
      rw [hstart,hb]
      simp only [giantSignedPerformedBirthTime,Fin.val_succ]
      omega)
    exact congrArg offset he.symm
  · have he : L.start = a.1 := Fin.ext (by
      rw [hstart,hb]
      simp only [giantSignedPerformedBirthTime]
      omega)
    exact congrArg offset he.symm

include ha hd in
theorem active_offset (i : Fin (n+1)) (hi : GiantSignedChronologicalActive h i g p) :
    let offset := giantSignedChronologicalOffset κ h
    (offset i : ZMod p.val) = (offset L.start : ZMod p.val) := by
  let o := giantSignedChronologicalOffset κ h
  obtain ⟨j,hj⟩ := hi
  let l := giantSignedChronologicalPreLineage h κ ha i g
  have hb : l.origin (.inl j) = L.birth :=
    hd ((l.prime_eq (.inl j)).trans ((congrArg Subtype.val hj).trans L.birth_prime.symm))
  have hz := giantSignedChronological_active_anchor κ h ha i g j
  change (o i : ZMod ((h.state i).2.1 g j).val) =
    (giantSignedBirthOffset o (giantSignedChronologicalBirthData h) (l.origin (.inl j)) :
      ZMod ((h.state i).2.1 g j).val) at hz
  rw [hb,L.birthOffset_eq] at hz
  exact (congrArg Subtype.val hj) ▸ hz

end GiantSignedChronologicalLifeEndpoints
end
end ArtinMatthews
