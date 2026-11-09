module

public import ArtinMatthews.GiantPrimeLifespanView


set_option backward.privateInPublic true
@[expose] public section

/-! Literal pending, ghost, and edge statuses of one chosen prime interval. -/

namespace ArtinMatthews
noncomputable section

variable {n : ℕ} {A : Finset (Fin n)} (c : GiantSignedResidueLifespanChoice A)

local notation "view" => giantSignedPrimeLifespanView A c

def giantSignedPrimePendingBefore (v : Fin n) : Prop :=
  Option.elim view False (fun L => L.start < v ∧ v ≤ L.finish ∧ v ∉ A)

def giantSignedPrimePendingAfter (v : Fin n) : Prop :=
  Option.elim view False (fun L => L.start ≤ v ∧ v < L.finish ∧ v ∉ A)

def giantSignedPrimeGhostBirthAt (v : Fin n) : Prop :=
  Option.elim view False (fun L => L.start = v ∧ L.ghostBirth = true)

def giantSignedPrimeGhostDeathAt (v : Fin n) : Prop :=
  Option.elim view False (fun L => L.finish = v ∧ L.ghostDeath = true)

def giantSignedPrimeStore (v w : Fin n) : Prop :=
  Option.elim view False (fun L => v ∈ A ∧ w ∉ A ∧ w ≤ L.finish)

def giantSignedPrimePromote (v w : Fin n) : Prop :=
  giantSignedPrimePendingAfter c v ∧ w ∈ A

def giantSignedPrimeFreshAt (v : Fin n) : Prop :=
  Option.elim view False (fun L => L.start = v ∧ v ∈ A)

/-- A vertex deletes its terminal ghost and appends its initial ghost. -/
theorem giantSignedPrimePendingAfter_ghostUpdate (v : Fin n) :
    giantSignedPrimePendingAfter c v ↔
      (giantSignedPrimePendingBefore c v ∧ ¬giantSignedPrimeGhostDeathAt c v) ∨
        giantSignedPrimeGhostBirthAt c v := by
  unfold giantSignedPrimePendingAfter giantSignedPrimePendingBefore
    giantSignedPrimeGhostDeathAt giantSignedPrimeGhostBirthAt
  cases view with
  | none => simp
  | some L =>
    change (L.start ≤ v ∧ v < L.finish ∧ v ∉ A) ↔
      ((L.start < v ∧ v ≤ L.finish ∧ v ∉ A) ∧ ¬(L.finish = v ∧ L.ghostDeath = true)) ∨
        (L.start = v ∧ L.ghostBirth = true)
    constructor
    · rintro ⟨hstart, hfinish, hvA⟩
      by_cases he : L.start = v
      · exact Or.inr ⟨he, L.ghostBirth_iff.mpr (fun hi => hvA (he ▸ hi))⟩
      · exact Or.inl ⟨⟨lt_of_le_of_ne hstart he, hfinish.le, hvA⟩,
          fun hd => not_lt_of_ge hd.1.le hfinish⟩
    · rintro (⟨⟨hstart, hfinish, hvA⟩, hD⟩ | ⟨he, hB⟩)
      · have hne : v ≠ L.finish := fun hv =>
          hD ⟨hv.symm, L.ghostDeath_iff.mpr (fun hi => hvA (hv.symm ▸ hi))⟩
        exact ⟨hstart.le, lt_of_le_of_ne hfinish hne, hvA⟩
      · exact ⟨he.le, he ▸ L.ghostBirth_strict hB, he ▸ L.ghostBirth_iff.mp hB⟩

theorem giantSignedPrimeGhostBirthAt_not_pendingBefore (v : Fin n)
    (h : giantSignedPrimeGhostBirthAt c v) : ¬giantSignedPrimePendingBefore c v := by
  unfold giantSignedPrimeGhostBirthAt at h
  unfold giantSignedPrimePendingBefore
  cases hv : view with
  | none => simp
  | some L =>
    rw [hv] at h
    exact fun hp => not_lt_of_ge h.1.ge hp.1

theorem giantSignedPrimeGhostDeathAt_pendingBefore (v : Fin n)
    (h : giantSignedPrimeGhostDeathAt c v) : giantSignedPrimePendingBefore c v := by
  unfold giantSignedPrimeGhostDeathAt at h
  unfold giantSignedPrimePendingBefore
  cases hv : view with
  | none =>
    rw [hv] at h
    exact h.elim
  | some L =>
    rw [hv] at h
    exact ⟨h.1 ▸ L.ghostDeath_strict h.2, h.1.ge, h.1 ▸ L.ghostDeath_iff.mp h.2⟩

theorem giantSignedPrimeGhostEndpoints_disjoint (v : Fin n) :
    ¬(giantSignedPrimeGhostBirthAt c v ∧ giantSignedPrimeGhostDeathAt c v) := by
  rintro ⟨hB, hD⟩
  exact giantSignedPrimeGhostBirthAt_not_pendingBefore c v hB
    (giantSignedPrimeGhostDeathAt_pendingBefore c v hD)

private theorem lt_adjacent_iff_le {v w i : Fin n} (h : v.val + 1 = w.val) :
    i < w ↔ i ≤ v := by
  change i.val < w.val ↔ i.val ≤ v.val
  omega

private theorem lt_after_iff_le_adjacent {v w i : Fin n} (h : v.val + 1 = w.val) :
    v < i ↔ w ≤ i := by
  change v.val < i.val ↔ w.val ≤ i.val
  omega

/-- The next pending population consists of surviving pending particles
and departing active particles whose interval continues. -/
theorem giantSignedPrimePendingBefore_adjacent (v w : Fin n) (hAdj : v.val + 1 = w.val) :
    giantSignedPrimePendingBefore c w ↔
      (giantSignedPrimePendingAfter c v ∧ w ∉ A) ∨ giantSignedPrimeStore c v w := by
  unfold giantSignedPrimePendingBefore giantSignedPrimePendingAfter giantSignedPrimeStore
  cases view with
  | none => simp
  | some L =>
    change (L.start < w ∧ w ≤ L.finish ∧ w ∉ A) ↔
      ((L.start ≤ v ∧ v < L.finish ∧ v ∉ A) ∧ w ∉ A) ∨
        (v ∈ A ∧ w ∉ A ∧ w ≤ L.finish)
    rw [lt_adjacent_iff_le hAdj, lt_after_iff_le_adjacent hAdj]
    have hl : v ∈ A → L.start ≤ v := fun hv => (L.active_contained v hv).1
    tauto

theorem giantSignedPrimeSurviveStore_disjoint (v w : Fin n) :
    ¬((giantSignedPrimePendingAfter c v ∧ w ∉ A) ∧ giantSignedPrimeStore c v w) := by
  unfold giantSignedPrimePendingAfter giantSignedPrimeStore
  cases view with
  | none => simp
  | some L =>
    change ¬(((L.start ≤ v ∧ v < L.finish ∧ v ∉ A) ∧ w ∉ A) ∧
      (v ∈ A ∧ w ∉ A ∧ w ≤ L.finish))
    tauto

/-- A newly active visit either promotes the pending particle or starts a
first active lifespan. -/
theorem giantSignedPrimeNewActive_adjacent (v w : Fin n) (hAdj : v.val + 1 = w.val) :
    w ∈ A ∧ v ∉ A ↔ giantSignedPrimePromote c v w ∨ giantSignedPrimeFreshAt c w := by
  have hvw : v < w := by
    change v.val < w.val
    omega
  unfold giantSignedPrimePromote giantSignedPrimePendingAfter giantSignedPrimeFreshAt
  cases hL : view with
  | none =>
    have hA := giantSignedPrimeLifespanView_none_empty A c hL
    simp [hA]
  | some L =>
    change (w ∈ A ∧ v ∉ A) ↔
      ((L.start ≤ v ∧ v < L.finish ∧ v ∉ A) ∧ w ∈ A) ∨ (L.start = w ∧ w ∈ A)
    constructor
    · rintro ⟨hwA, hvA⟩
      have hbounds := L.active_contained w hwA
      by_cases he : L.start = w
      · exact Or.inr ⟨he, hwA⟩
      · have hstart := (lt_adjacent_iff_le hAdj).mp (lt_of_le_of_ne hbounds.1 he)
        exact Or.inl ⟨⟨hstart, hvw.trans_le hbounds.2, hvA⟩, hwA⟩
    · rintro (⟨⟨_, _, hvA⟩, hwA⟩ | ⟨he, hwA⟩)
      · exact ⟨hwA, hvA⟩
      · refine ⟨hwA, fun hvA => ?_⟩
        have hle := (L.active_contained v hvA).1
        rw [he] at hle
        exact not_lt_of_ge hle hvw

theorem giantSignedPrimePromoteFresh_disjoint (v w : Fin n) (hAdj : v.val + 1 = w.val) :
    ¬(giantSignedPrimePromote c v w ∧ giantSignedPrimeFreshAt c w) := by
  have hvw : v < w := by
    change v.val < w.val
    omega
  unfold giantSignedPrimePromote giantSignedPrimePendingAfter giantSignedPrimeFreshAt
  cases view with
  | none => simp
  | some L =>
    change ¬(((L.start ≤ v ∧ v < L.finish ∧ v ∉ A) ∧ w ∈ A) ∧ (L.start = w ∧ w ∈ A))
    rintro ⟨⟨⟨hle, _, _⟩, _⟩, he, _⟩
    rw [he] at hle
    exact not_lt_of_ge hle hvw

/-- Fresh active birth is exactly the first active visit with no earlier ghost. -/
theorem giantSignedPrimeFreshAt_iff_first (hA : A.Nonempty) (v : Fin n) :
    giantSignedPrimeFreshAt c v ↔
      (giantSignedResidueLifespanActiveEquiv A hA c).1 = none ∧ v = A.min' hA := by
  unfold giantSignedPrimeFreshAt
  rw [giantSignedPrimeLifespanView_active A c hA]
  let e := giantSignedResidueLifespanActiveEquiv A hA c
  change (giantSignedPrimeStart (A.min' hA) e.1 = v ∧ v ∈ A) ↔ e.1 = none ∧ v = A.min' hA
  cases e.1 with
  | none =>
    constructor
    · rintro ⟨h, _⟩
      exact ⟨rfl, h.symm⟩
    · rintro ⟨_, h⟩
      exact ⟨h.symm, h.symm ▸ A.min'_mem hA⟩
  | some l =>
    constructor
    · rintro ⟨h, hvA⟩
      change l.val = v at h
      have hlA : l.val ∈ A := h.symm ▸ hvA
      exact (not_lt_of_ge (A.min'_le l.val hlA) (Finset.mem_filter.mp l.property).2).elim
    · rintro ⟨h, _⟩
      cases h

theorem giantSignedPrimePendingBefore_first {N : ℕ} {A : Finset (Fin (N + 1))}
    (c : GiantSignedResidueLifespanChoice A) : ¬giantSignedPrimePendingBefore c 0 := by
  unfold giantSignedPrimePendingBefore
  cases giantSignedPrimeLifespanView A c with
  | none => simp
  | some L =>
    intro h
    have hl := h.1
    change L.start.val < 0 at hl
    omega

theorem giantSignedPrimePendingAfter_last {N : ℕ} {A : Finset (Fin (N + 1))}
    (c : GiantSignedResidueLifespanChoice A) : ¬giantSignedPrimePendingAfter c (Fin.last N) := by
  unfold giantSignedPrimePendingAfter
  cases giantSignedPrimeLifespanView A c with
  | none => simp
  | some L =>
    intro h
    have hu := h.2.1
    change N < L.finish.val at hu
    have hbound := L.finish.isLt
    omega

end
end ArtinMatthews
