module

public import ArtinMatthews.GiantResidueLifespanChoice


set_option backward.privateInPublic true
@[expose] public section

/-! A represented choice carries its literal interval and ghost flags. -/

namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

structure GiantSignedPrimeLifespanInterval {n : ℕ} (A : Finset (Fin n)) where
  start : Fin n
  finish : Fin n
  ghostBirth : Bool
  ghostDeath : Bool
  start_le_finish : start ≤ finish
  active_contained : ∀ i ∈ A, start ≤ i ∧ i ≤ finish
  ghostBirth_iff : ghostBirth = true ↔ start ∉ A
  ghostDeath_iff : ghostDeath = true ↔ finish ∉ A
  ghostBirth_strict : ghostBirth = true → start < finish
  ghostDeath_strict : ghostDeath = true → start < finish

/-- The active view retains the exact optional endpoint flags. -/
def giantSignedActiveLifespanInterval {n : ℕ} (A : Finset (Fin n)) (hA : A.Nonempty)
    (c : GiantSignedPrimeActiveEndpointChoice A hA) : GiantSignedPrimeLifespanInterval A where
  start := giantSignedPrimeStart (A.min' hA) c.1
  finish := giantSignedPrimeEnd (A.max' hA) c.2
  ghostBirth := c.1.isSome
  ghostDeath := c.2.isSome
  start_le_finish := (giantSignedPrimeStart_le _ _).trans
    ((A.min'_le_max' hA).trans (giantSignedPrimeEnd_ge _ _))
  active_contained := giantSignedPrimeActiveEndpoint_bounds A hA c
  ghostBirth_iff := by
    cases c.1 with
    | none =>
      change false = true ↔ A.min' hA ∉ A
      simp [A.min'_mem hA]
    | some l =>
      have hlt := (Finset.mem_filter.mp l.property).2
      have hn : l.val ∉ A := fun hl => not_lt_of_ge (A.min'_le l.val hl) hlt
      change true = true ↔ l.val ∉ A
      simp [hn]
  ghostDeath_iff := by
    cases c.2 with
    | none =>
      change false = true ↔ A.max' hA ∉ A
      simp [A.max'_mem hA]
    | some u =>
      have hlt := (Finset.mem_filter.mp u.property).2
      have hn : u.val ∉ A := fun hu => not_lt_of_ge (A.le_max' u.val hu) hlt
      change true = true ↔ u.val ∉ A
      simp [hn]
  ghostBirth_strict := by
    cases c.1 with
    | none => simp
    | some l =>
      intro _
      exact (Finset.mem_filter.mp l.property).2.trans_le
        ((A.min'_le_max' hA).trans (giantSignedPrimeEnd_ge _ _))
  ghostDeath_strict := by
    cases c.2 with
    | none => simp
    | some u =>
      intro _
      exact ((giantSignedPrimeStart_le _ _).trans (A.min'_le_max' hA)).trans_lt
        (Finset.mem_filter.mp u.property).2

/-- The represented orphan has two strict ghost endpoints. -/
def giantSignedOrphanLifespanInterval {n : ℕ} (A : Finset (Fin n)) (hA : ¬A.Nonempty)
    (c : GiantSignedPrimeOrphanEndpointChoice n) : GiantSignedPrimeLifespanInterval A where
  start := c.1
  finish := c.2.1
  ghostBirth := true
  ghostDeath := true
  start_le_finish := (giantSignedPrimeOrphanEndpoint_strict c).le
  active_contained := fun i hi => (hA ⟨i, hi⟩).elim
  ghostBirth_iff := by
    have hn : c.1 ∉ A := fun h => hA ⟨c.1, h⟩
    simp [hn]
  ghostDeath_iff := by
    have hn : c.2.1 ∉ A := fun h => hA ⟨c.2.1, h⟩
    simp [hn]
  ghostBirth_strict := fun _ => giantSignedPrimeOrphanEndpoint_strict c
  ghostDeath_strict := fun _ => giantSignedPrimeOrphanEndpoint_strict c

/-- Absence has no interval. Active and orphan choices retain their endpoints. -/
def giantSignedPrimeLifespanView {n : ℕ} (A : Finset (Fin n))
    (c : GiantSignedResidueLifespanChoice A) : Option (GiantSignedPrimeLifespanInterval A) :=
  if hA : A.Nonempty then
    some (giantSignedActiveLifespanInterval A hA (giantSignedResidueLifespanActiveEquiv A hA c))
  else
    (giantSignedResidueLifespanInactiveEquiv A hA c).map (giantSignedOrphanLifespanInterval A hA)

theorem giantSignedPrimeLifespanView_active {n : ℕ} (A : Finset (Fin n))
    (c : GiantSignedResidueLifespanChoice A) (hA : A.Nonempty) :
    giantSignedPrimeLifespanView A c =
      some (giantSignedActiveLifespanInterval A hA (giantSignedResidueLifespanActiveEquiv A hA c)) := by
  rw [giantSignedPrimeLifespanView, dite_eq_left hA]

theorem giantSignedPrimeLifespanView_inactive {n : ℕ} (A : Finset (Fin n))
    (c : GiantSignedResidueLifespanChoice A) (hA : ¬A.Nonempty) :
    giantSignedPrimeLifespanView A c =
      (giantSignedResidueLifespanInactiveEquiv A hA c).map (giantSignedOrphanLifespanInterval A hA) := by
  rw [giantSignedPrimeLifespanView, dite_eq_right hA]

theorem giantSignedPrimeLifespanView_none_empty {n : ℕ} (A : Finset (Fin n))
    (c : GiantSignedResidueLifespanChoice A) (h : giantSignedPrimeLifespanView A c = none) : A = ∅ := by
  by_cases hA : A.Nonempty
  · rw [giantSignedPrimeLifespanView_active A c hA] at h
    cases h
  · exact Finset.not_nonempty_iff_eq_empty.mp hA

theorem giantSignedPrimeLifespanView_of_active {n : ℕ} (A : Finset (Fin n))
    (c : GiantSignedResidueLifespanChoice A) (i : Fin n) (hi : i ∈ A) :
    ∃ L, giantSignedPrimeLifespanView A c = some L ∧ L.start ≤ i ∧ i ≤ L.finish := by
  let hA : A.Nonempty := ⟨i, hi⟩
  let L := giantSignedActiveLifespanInterval A hA (giantSignedResidueLifespanActiveEquiv A hA c)
  exact ⟨L, giantSignedPrimeLifespanView_active A c hA, L.active_contained i hi⟩

theorem giantSignedPrimeLifespanInterval_orphan {n : ℕ} {A : Finset (Fin n)}
    (L : GiantSignedPrimeLifespanInterval A) (hA : ¬A.Nonempty) :
    L.start < L.finish ∧ L.ghostBirth = true ∧ L.ghostDeath = true := by
  have hB := L.ghostBirth_iff.mpr (fun h => hA ⟨L.start, h⟩)
  have hD := L.ghostDeath_iff.mpr (fun h => hA ⟨L.finish, h⟩)
  exact ⟨L.ghostBirth_strict hB, hB, hD⟩

end
end ArtinMatthews
