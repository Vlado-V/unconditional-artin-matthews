module

public import ArtinMatthews.GiantSignedChronologicalLiveTransitions
public import ArtinMatthews.GiantPrimeLifespanView


set_option backward.privateInPublic true
@[expose] public section

/-! The endpoints of a chronological lifetime retain its literal
birth and final live half-step. Activity distinguishes the ghost flags. -/

namespace ArtinMatthews
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}
    (h : GiantSignedChronologicalChoices PS PB ell C batch)

structure GiantSignedChronologicalLifeEndpoints (g : B) (p : PB g) where
  birth : GiantSignedPerformedBirth (giantSignedChronologicalBirthData h)
  birth_group : giantSignedPerformedBirthGroup (h := h) birth = g
  birth_prime : giantSignedPerformedBirthPrime (giantSignedChronologicalBirthData h) birth = p.val
  endTime : ℕ
  endTime_le : endTime ≤ 2*n+1
  live : ∀ t, GiantSignedChronologicalLiveAt h g p t ↔
    giantSignedPerformedBirthTime (giantSignedChronologicalBirthData h) birth ≤ t ∧ t ≤ endTime

namespace GiantSignedChronologicalLifeEndpoints

variable {h} {g : B} {p : PB g}
    (L : GiantSignedChronologicalLifeEndpoints h g p)

def startTime : ℕ := giantSignedPerformedBirthTime (giantSignedChronologicalBirthData h) L.birth

theorem startTime_le : L.startTime ≤ L.endTime :=
  ((L.live _).mp (giantSignedChronologicalLiveAt_birth h g p L.birth L.birth_group L.birth_prime)).2

def start : Fin (n+1) := ⟨L.startTime / 2, by have := L.startTime_le.trans L.endTime_le; omega⟩

def finish : Fin (n+1) := ⟨L.endTime / 2, by have := L.endTime_le; omega⟩

theorem start_val : L.start.val = L.startTime / 2 := rfl

theorem finish_val : L.finish.val = L.endTime / 2 := rfl

theorem active_bounds (i : Fin (n+1)) (hi : GiantSignedChronologicalActive h i g p) :
    L.start ≤ i ∧ i ≤ L.finish := by
  have h1 := (L.live _).mp ((giantSignedChronologicalLiveAt_before_iff h i g p).mpr (Or.inl hi))
  have h2 := (L.live _).mp ((giantSignedChronologicalLiveAt_after_iff h i g p).mpr (Or.inl hi))
  change L.startTime ≤ 2*i.val ∧ 2*i.val ≤ L.endTime at h1
  change L.startTime ≤ 2*i.val+1 ∧ 2*i.val+1 ≤ L.endTime at h2
  change L.start.val ≤ i.val ∧ i.val ≤ L.finish.val
  rw [L.start_val,L.finish_val]
  omega

theorem start_active_of_even (hEven : L.startTime % 2 = 0) :
    GiantSignedChronologicalActive h L.start g p := by
  have hg := L.birth_group
  have hp := L.birth_prime
  cases hb : L.birth with
  | inl a =>
    obtain ⟨g',j⟩ := a
    rw [hb] at hg hp
    change g' = g at hg
    subst g'
    have hs : L.start = 0 := by
      apply Fin.ext
      simp only [start_val,startTime,hb,giantSignedPerformedBirthTime,Nat.zero_div,Fin.val_zero]
    exact hs.symm ▸ (show GiantSignedChronologicalActive h 0 g p from ⟨j,Subtype.ext hp⟩)
  | inr a =>
    rcases a with ⟨i,g',j⟩ | ⟨i,g',j⟩
    · rw [hb] at hg hp
      change g' = g at hg
      subst g'
      have hs : L.start = i.succ := by
        apply Fin.ext
        simp only [start_val,startTime,hb,giantSignedPerformedBirthTime,Fin.val_succ]
        omega
      let slot := giantTwoSidedPatternFreeSlot (C i g) ell (giantSignedPatternFreeSlotEquiv (C i g) ell j.val)
      exact hs.symm ▸ (show GiantSignedChronologicalActive h i.succ g p from
        ⟨h.targetBigPermutation i g slot,Subtype.ext hp⟩)
    · simp only [startTime,hb,giantSignedPerformedBirthTime] at hEven
      omega

theorem start_inactive_iff : ¬GiantSignedChronologicalActive h L.start g p ↔ L.startTime % 2 = 1 := by
  constructor
  · intro hn
    by_contra hodd
    exact hn (L.start_active_of_even (by omega))
  · intro hodd ha
    have h := (L.live _).mp ((giantSignedChronologicalLiveAt_before_iff h L.start g p).mpr (Or.inl ha))
    change L.startTime ≤ 2*L.start.val ∧ _ at h
    rw [L.start_val] at h
    omega

theorem finish_active_of_odd (κ : Fin n → ℤ) (ha : GiantSignedChronologicalAdmissible κ h)
    (hOdd : L.endTime % 2 = 1) : GiantSignedChronologicalActive h L.finish g p := by
  have ht : L.endTime = 2*L.finish.val+1 := by rw [L.finish_val]; omega
  have he : GiantSignedChronologicalLiveAt h g p L.endTime :=
    (L.live _).mpr ⟨L.startTime_le,le_rfl⟩
  rw [ht] at he
  rcases (giantSignedChronologicalLiveAt_after_iff h L.finish g p).mp he with hActive | hPending
  · exact hActive
  · by_cases hl : L.finish = Fin.last n
    · exact (giantSignedChronologicalPendingAfter_last h κ ha g p (hl ▸ hPending)).elim
    · have hi : L.finish.val < n := by
        have hh : L.finish.val ≠ n := fun hf => hl (Fin.ext hf)
        have := L.finish.isLt
        omega
      let i : Fin n := ⟨L.finish.val,hi⟩
      have hi' : L.finish = i.castSucc := Fin.ext rfl
      have hx := giantSignedChronologicalPendingAfter_lives_next h κ ha i g p (hi' ▸ hPending)
      have hs := ((L.live _).mp hx).2
      change 2*(L.finish.val+1) ≤ L.endTime at hs
      omega

theorem finish_inactive_iff (κ : Fin n → ℤ) (ha : GiantSignedChronologicalAdmissible κ h) :
    ¬GiantSignedChronologicalActive h L.finish g p ↔ L.endTime % 2 = 0 := by
  constructor
  · intro hn
    by_contra heven
    exact hn (L.finish_active_of_odd κ ha (by omega))
  · intro heven hActive
    have he := ((L.live _).mp ((giantSignedChronologicalLiveAt_after_iff h L.finish g p).mpr (Or.inl hActive))).2
    rw [L.finish_val] at he
    omega

def interval (κ : Fin n → ℤ) (ha : GiantSignedChronologicalAdmissible κ h)
    (A : Finset (Fin (n+1))) (hA : ∀ i, i ∈ A ↔ GiantSignedChronologicalActive h i g p) :
    GiantSignedPrimeLifespanInterval A := by
  classical
  have hle : L.start ≤ L.finish := by
    change L.start.val ≤ L.finish.val
    rw [L.start_val,L.finish_val]
    have := L.startTime_le
    omega
  have hB : (decide (L.startTime % 2 = 1)) = true ↔ L.start ∉ A := by
    rw [decide_eq_true_eq,hA]
    exact L.start_inactive_iff.symm
  have hD : (decide (L.endTime % 2 = 0)) = true ↔ L.finish ∉ A := by
    rw [decide_eq_true_eq,hA]
    exact (L.finish_inactive_iff κ ha).symm
  have hstrict (hs : L.start ∉ A) : L.start < L.finish := by
    refine lt_of_le_of_ne hle (fun he => ?_)
    have ho := L.start_inactive_iff.mp (fun hActive => hs ((hA _).mpr hActive))
    have hf := (L.finish_inactive_iff κ ha).mp (fun hActive => hs ((hA _).mpr (he.symm ▸ hActive)))
    have hval := congrArg Fin.val he
    rw [L.start_val,L.finish_val] at hval
    have htime := L.startTime_le
    omega
  exact ⟨L.start,L.finish,decide (L.startTime % 2 = 1),decide (L.endTime % 2 = 0),hle,
    fun i hi => L.active_bounds i ((hA i).mp hi),hB,hD,
    fun hb => hstrict (hB.mp hb),fun hd => lt_of_le_of_ne hle (fun he =>
      (ne_of_lt (hstrict (fun hs => (hD.mp hd) (he ▸ hs)))) he)⟩

end GiantSignedChronologicalLifeEndpoints
end
end ArtinMatthews
