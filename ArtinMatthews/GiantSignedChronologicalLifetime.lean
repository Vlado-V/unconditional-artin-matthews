module

public import ArtinMatthews.GiantSignedChronologicalLineage


set_option backward.privateInPublic true
@[expose] public section

/-! A prime in a birth-distinct chronology is live on an actual interval
of half-step times. Even times precede a visit and odd times follow it. -/

namespace ArtinMatthews
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}
    (h : GiantSignedChronologicalChoices PS PB ell C batch)

def GiantSignedChronologicalLiveAt (g : B) (p : PB g) (t : ℕ) : Prop :=
  (∃ i : Fin (n+1), t = 2*i.val ∧
    ∃ z, giantSignedStateLivePrime (h.state i) g z = p) ∨
  (∃ i : Fin (n+1), t = 2*i.val+1 ∧
    ∃ z, giantSignedStateLivePrime (giantSignedChronologicalAfterVisitState h i) g z = p)

theorem giantSignedChronologicalLiveAt_before (g : B) (p : PB g) (i : Fin (n+1)) :
    GiantSignedChronologicalLiveAt h g p (2*i.val) ↔
      ∃ z, giantSignedStateLivePrime (h.state i) g z = p := by
  constructor
  · rintro (⟨j,hj,hz⟩ | ⟨j,hj,_⟩)
    · have he : j = i := Fin.ext (by omega)
      exact he ▸ hz
    · omega
  · exact fun hz => Or.inl ⟨i,rfl,hz⟩

theorem giantSignedChronologicalLiveAt_after (g : B) (p : PB g) (i : Fin (n+1)) :
    GiantSignedChronologicalLiveAt h g p (2*i.val+1) ↔
      ∃ z, giantSignedStateLivePrime (giantSignedChronologicalAfterVisitState h i) g z = p := by
  constructor
  · rintro (⟨j,hj,_⟩ | ⟨j,hj,hz⟩)
    · omega
    · have he : j = i := Fin.ext (by omega)
      exact he ▸ hz
  · exact fun hz => Or.inr ⟨i,rfl,hz⟩

theorem giantSignedChronologicalLiveAt_bound (g : B) (p : PB g) {t : ℕ}
    (ht : GiantSignedChronologicalLiveAt h g p t) : t ≤ 2*n+1 := by
  rcases ht with ⟨i,hi,_⟩ | ⟨i,hi,_⟩ <;> have := i.isLt <;> omega

variable {h}

def giantSignedPerformedBirthGroup (b : GiantSignedPerformedBirth (giantSignedChronologicalBirthData h)) : B :=
  match b with
  | .inl a => a.1
  | .inr (.inl a) => a.2.1
  | .inr (.inr a) => a.2.1

theorem giantSignedPerformedBirthPrime_mem_group
    (b : GiantSignedPerformedBirth (giantSignedChronologicalBirthData h)) :
    giantSignedPerformedBirthPrime (giantSignedChronologicalBirthData h) b ∈
      PB (giantSignedPerformedBirthGroup (h := h) b) := by
  rcases b with a | (a | a)
  · exact ((h.state 0).2.1 a.1 a.2).property
  · exact (giantSignedPatternFreeLabels (C a.1) (giantSignedChronologicalBigTarget h a.1)
      a.2.1 a.2.2.val).property
  · exact (h.born a.1 a.2.1 a.2.2).property

variable (h)

local notation "BirthData" => giantSignedChronologicalBirthData h

theorem giantSignedChronologicalLiveAt_birth (g : B) (p : PB g)
    (b : GiantSignedPerformedBirth BirthData) (hgroup : giantSignedPerformedBirthGroup (h := h) b = g)
    (hp : giantSignedPerformedBirthPrime BirthData b = p.val) :
    GiantSignedChronologicalLiveAt h g p (giantSignedPerformedBirthTime BirthData b) := by
  rcases b with ⟨g',j⟩ | (⟨i,g',j⟩ | ⟨i,g',j⟩)
  · change g' = g at hgroup
    subst g'
    exact Or.inl ⟨0,rfl,.inl j,Subtype.ext hp⟩
  · change g' = g at hgroup
    subst g'
    let slot := giantTwoSidedPatternFreeSlot (C i g) ell (giantSignedPatternFreeSlotEquiv (C i g) ell j.val)
    exact Or.inl ⟨i.succ,by simp only [giantSignedPerformedBirthTime,Fin.val_succ]; omega,
      .inl (h.targetBigPermutation i g slot),Subtype.ext hp⟩
  · change g' = g at hgroup
    subst g'
    refine Or.inr ⟨i,rfl,.inr (Fin.natAdd ((h.deleted i g)ᶜ).card j),?_⟩
    change ((giantSignedChronologicalGhostTarget h i).2 g (Fin.natAdd ((h.deleted i g)ᶜ).card j)).1 = p
    rw [giantSignedChronologicalGhostTarget_born]
    exact Subtype.ext hp

theorem giantSignedChronologicalLiveAt_origin (κ : Fin n → ℤ) (ha : GiantSignedChronologicalAdmissible κ h)
    (g : B) (p : PB g) {t : ℕ}
    (ht : GiantSignedChronologicalLiveAt h g p t) :
    ∃ b : GiantSignedPerformedBirth BirthData,
      giantSignedPerformedBirthPrime BirthData b = p.val ∧ giantSignedPerformedBirthTime BirthData b ≤ t := by
  rcases ht with ⟨i,rfl,z,hz⟩ | ⟨i,rfl,z,hz⟩
  · let l := giantSignedChronologicalPreLineage h κ ha i g
    exact ⟨l.origin z, (l.prime_eq z).trans (congrArg Subtype.val hz), l.time_le z⟩
  · let l := giantSignedChronologicalVisitLineage h i g (giantSignedChronologicalPreLineage h κ ha i g)
    exact ⟨l.origin z, (l.prime_eq z).trans (congrArg Subtype.val hz), l.time_le z⟩

theorem giantSignedChronologicalLiveAt_time_ge_birth (κ : Fin n → ℤ) (ha : GiantSignedChronologicalAdmissible κ h)
    (hd : GiantSignedBirthDistinct BirthData) (g : B) (p : PB g)
    (b : GiantSignedPerformedBirth BirthData) (hp : giantSignedPerformedBirthPrime BirthData b = p.val) {t : ℕ}
    (ht : GiantSignedChronologicalLiveAt h g p t) : giantSignedPerformedBirthTime BirthData b ≤ t := by
  obtain ⟨b',hb',ht'⟩ := giantSignedChronologicalLiveAt_origin h κ ha g p ht
  have he : b' = b := hd (hb'.trans hp.symm)
  exact he ▸ ht'

theorem giantSignedChronologicalLiveAt_previous (κ : Fin n → ℤ) (ha : GiantSignedChronologicalAdmissible κ h)
    (hd : GiantSignedBirthDistinct BirthData) (g : B) (p : PB g)
    (b : GiantSignedPerformedBirth BirthData) (hp : giantSignedPerformedBirthPrime BirthData b = p.val)
    {t : ℕ} (hb : giantSignedPerformedBirthTime BirthData b < t+1)
    (ht : GiantSignedChronologicalLiveAt h g p (t+1)) : GiantSignedChronologicalLiveAt h g p t := by
  rcases ht with ⟨v,hv,z,hz⟩ | ⟨v,hv,z,hz⟩
  · revert hv z
    refine Fin.cases ?_ (fun i => ?_) v
    · intro hv
      change t+1 = 0 at hv
      omega
    · intro hv z hz
      have he := giantSignedChronologicalEdgeOrigin_prime κ h ha i g z
      cases he' : giantSignedChronologicalEdgeOrigin κ h ha.compatible i g z with
      | inl u =>
        rw [he',Sum.elim_inl] at he
        exact Or.inr ⟨i.castSucc,by simp only [Fin.val_castSucc]; simp only [Fin.val_succ] at hv; omega,
          u,he.symm.trans hz⟩
      | inr u =>
        rw [he',Sum.elim_inr] at he
        let b' := giantSignedChronologicalEdgeBirth h i g u
        have hb' : b' = b := hd ((congrArg Subtype.val (he.symm.trans hz)).trans hp.symm)
        have ht' : giantSignedPerformedBirthTime BirthData b = 2*i.val+2 :=
          (congrArg (giantSignedPerformedBirthTime BirthData) hb').symm
        simp only [Fin.val_succ] at hv
        omega
  · have he := giantSignedChronologicalVisitOrigin_prime h v g z
    cases he' : giantSignedChronologicalVisitOrigin h v g z with
    | inl u =>
      rw [he',Sum.elim_inl] at he
      exact Or.inl ⟨v,by omega,u,he.symm.trans hz⟩
    | inr u =>
      rw [he',Sum.elim_inr] at he
      let b' := giantSignedChronologicalVisitBirth h v g u
      have hb' : b' = b := hd ((congrArg Subtype.val (he.symm.trans hz)).trans hp.symm)
      have ht' : giantSignedPerformedBirthTime BirthData b = 2*v.val+1 :=
        (congrArg (giantSignedPerformedBirthTime BirthData) hb').symm
      omega

theorem giantSignedChronologicalLiveAt_interval (κ : Fin n → ℤ) (ha : GiantSignedChronologicalAdmissible κ h)
    (hd : GiantSignedBirthDistinct BirthData) (g : B) (p : PB g)
    (b : GiantSignedPerformedBirth BirthData) (hgroup : giantSignedPerformedBirthGroup (h := h) b = g)
    (hp : giantSignedPerformedBirthPrime BirthData b = p.val) :
    ∃ finish ≤ 2*n+1, ∀ t, GiantSignedChronologicalLiveAt h g p t ↔
      giantSignedPerformedBirthTime BirthData b ≤ t ∧ t ≤ finish := by
  classical
  let start := giantSignedPerformedBirthTime BirthData b
  let live := (Finset.range (2*n+2)).filter (GiantSignedChronologicalLiveAt h g p)
  have hmem (t : ℕ) : t ∈ live ↔ GiantSignedChronologicalLiveAt h g p t := by
    simp only [live,Finset.mem_filter,Finset.mem_range]
    exact ⟨And.right,fun ht => ⟨Nat.lt_succ_of_le (giantSignedChronologicalLiveAt_bound h g p ht),ht⟩⟩
  have hs : start ∈ live := (hmem _).mpr (giantSignedChronologicalLiveAt_birth h g p b hgroup hp)
  let finish := live.max' ⟨start,hs⟩
  have hf := (hmem finish).mp (live.max'_mem ⟨start,hs⟩)
  have hfill (d : ℕ) : ∀ t, t+d = finish → start ≤ t → GiantSignedChronologicalLiveAt h g p t := by
    induction d with
    | zero =>
      intro t he _
      simp only [Nat.add_zero] at he
      exact he.symm ▸ hf
    | succ d ih =>
      intro t he ht
      apply giantSignedChronologicalLiveAt_previous h κ ha hd g p b hp (by change start < t+1; omega)
      exact ih (t+1) (by omega) (by omega)
  refine ⟨finish,giantSignedChronologicalLiveAt_bound h g p hf,fun t => ⟨?_,?_⟩⟩
  · intro ht
    exact ⟨giantSignedChronologicalLiveAt_time_ge_birth h κ ha hd g p b hp ht,
      live.le_max' _ ((hmem t).mpr ht)⟩
  · rintro ⟨ht,he⟩
    exact hfill (finish-t) t (by omega) ht

end
end ArtinMatthews
