module

public import ArtinMatthews.MarkedMemoryHistoryBirthLabels


set_option backward.privateInPublic true
@[expose] public section

/-! Group labels follow actual indexed particle origins through slots,
ghosts and edges, and hence along every natural-time chronological trace.
No numeric distinctness or nonzero-weight assumption is needed. -/
namespace ArtinMatthews
noncomputable section

def markedMemoryPopulationGroup {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (s : MarkedRawState P M B Z) : MarkedMemoryPopulationIndex s → J :=
  Sum.elim Sigma.fst Sigma.fst

@[simp] theorem markedMemoryPopulationGroup_active {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (s : MarkedRawState P M B Z) (j : J) (i : Fin M) :
    markedMemoryPopulationGroup s (Sum.inl ⟨j,i⟩) = j := rfl

@[simp] theorem markedMemoryPopulationGroup_pending {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (s : MarkedRawState P M B Z) (j : J) (i : Fin (s.2.2.1.1 j : ℕ)) :
    markedMemoryPopulationGroup s (Sum.inr ⟨j,i⟩) = j := rfl

def markedMemoryGhostBirthGroup {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2} {s : MarkedRawState P M B Z}
    (choice : MarkedMemoryGhostChoice hZ s) : MarkedMemoryGhostBirthIndex choice → J :=
  Sigma.fst

def markedMemoryEdgeBirthGroup {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2} {s : MarkedRawState P (pads+1) B Z}
    (choice : MarkedMemoryEdgeChoice hZ s) : MarkedMemoryEdgeBirthIndex choice → J :=
  Subtype.val

theorem markedMemorySlotPopulationEquiv_group {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (σ : J → Equiv.Perm (Fin M)) (s : MarkedRawState P M B Z)
    (i : MarkedMemoryPopulationIndex (markedRawSlotEquiv σ s)) :
    markedMemoryPopulationGroup s (markedMemorySlotPopulationEquiv σ s i) =
      markedMemoryPopulationGroup (markedRawSlotEquiv σ s) i := by
  rcases i with ⟨j,i⟩ | ⟨j,i⟩ <;> rfl

theorem markedMemoryGhostPopulationOrigin_group {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P M B Z)
    (choice : MarkedMemoryGhostChoice hZ s)
    (i : MarkedMemoryPopulationIndex (markedMemoryGhostChoiceTarget hZ s choice)) :
    Sum.elim (markedMemoryPopulationGroup s) (markedMemoryGhostBirthGroup choice)
        (markedMemoryGhostPopulationOrigin hZ s choice i) =
      markedMemoryPopulationGroup (markedMemoryGhostChoiceTarget hZ s choice) i := by
  rcases i with ⟨j,i⟩ | ⟨j,i⟩
  · rfl
  · rw [markedMemoryGhostPopulationOrigin_pending]
    generalize ho : markedMemoryGhostOrigin s.2.2 choice.deletion choice.sizes j i = o
    cases o <;> rfl

theorem markedMemoryEdgePopulationOrigin_group {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s)
    (i : MarkedMemoryPopulationIndex (markedRawEdgeTargetState hZ s choice)) :
    Sum.elim (markedMemoryPopulationGroup s) (fun j => j.1)
        (markedMemoryEdgePopulationOrigin hZ s choice i) =
      markedMemoryPopulationGroup (markedRawEdgeTargetState hZ s choice) i := by
  rcases i with ⟨j,i⟩ | ⟨j,i⟩
  · rw [markedMemoryEdgePopulationOrigin_active]
    generalize ho : markedMemoryEdgeGroupOrigin hZ s choice j (Sum.inl i) = o
    rcases o with (old | old) | fresh <;> rfl
  · erw [markedMemoryEdgePopulationOrigin_pending hZ s choice j i]
    generalize ho : markedMemoryEdgeGroupOrigin hZ s choice j (Sum.inr i) = o
    rcases o with (old | old) | fresh <;> rfl

theorem markedMemoryEdgeSlotPopulationOrigin_group {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedMemoryEdgeChoice hZ s)
    (i : MarkedMemoryPopulationIndex (markedMemoryEdgeChoiceTarget hZ s choice)) :
    Sum.elim (markedMemoryPopulationGroup s) (markedMemoryEdgeBirthGroup choice)
        (markedMemoryEdgeSlotPopulationOrigin hZ s choice i) =
      markedMemoryPopulationGroup (markedMemoryEdgeChoiceTarget hZ s choice) i := by
  let i₀ := markedMemorySlotPopulationEquiv choice.2.2
    (markedRawEdgeTargetState hZ (markedRawSlotEquiv choice.1 s) choice.2.1) i
  have h := markedMemoryEdgePopulationOrigin_group hZ (markedRawSlotEquiv choice.1 s) choice.2.1 i₀
  have ht := markedMemorySlotPopulationEquiv_group choice.2.2
    (markedRawEdgeTargetState hZ (markedRawSlotEquiv choice.1 s) choice.2.1) i
  change Sum.elim (markedMemoryPopulationGroup s) (markedMemoryEdgeBirthGroup choice)
      (Sum.map (markedMemorySlotPopulationEquiv choice.1 s) id
        (markedMemoryEdgePopulationOrigin hZ (markedRawSlotEquiv choice.1 s) choice.2.1 i₀)) = _
  generalize ho : markedMemoryEdgePopulationOrigin hZ (markedRawSlotEquiv choice.1 s) choice.2.1 i₀ = o at h ⊢
  cases o with
  | inl old =>
    simp only [Sum.map_inl, Sum.elim_inl] at h ⊢
    exact (markedMemorySlotPopulationEquiv_group choice.1 s old).trans (h.trans ht)
  | inr birth =>
    simp only [Sum.map_inr, Sum.elim_inr, id_eq]
    exact h.trans ht

/-- The actual time-tagged birth has the group retained in its finite label. -/
def markedMemoryHistoryTraceBirthGroup {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (t : ℕ)
    (b : MarkedMemoryHistoryTraceBirth hZ history t) : J :=
  (markedMemoryHistoryBirthLabel hZ history (markedMemoryTraceBirthToFinite hZ history ⟨t,b⟩)).1

theorem markedMemoryHistoryTraceBirthEquiv_group {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s)
    (b : Σ t, MarkedMemoryHistoryTraceBirth hZ history t) :
    (markedMemoryHistoryBirthLabel hZ history (markedMemoryHistoryTraceBirthEquiv hZ history b)).1 =
      markedMemoryHistoryTraceBirthGroup hZ history b.1 b.2 := rfl

theorem markedMemoryHistoryTraceStep_group {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (t : ℕ)
    (i : MarkedMemoryPopulationIndex (markedMemoryHistoryTraceState hZ history (t+1))) :
    Sum.elim (markedMemoryPopulationGroup (markedMemoryHistoryTraceState hZ history t))
      (markedMemoryHistoryTraceBirthGroup hZ history t) (markedMemoryHistoryTraceStep hZ history t i) =
        markedMemoryPopulationGroup (markedMemoryHistoryTraceState hZ history (t+1)) i := by
  induction n generalizing s t with
  | zero =>
    cases t with
    | zero => exact markedMemoryGhostPopulationOrigin_group hZ s history i
    | succ t => rfl
  | succ n ih =>
    cases t with
    | zero => exact markedMemoryGhostPopulationOrigin_group hZ s history.1 i
    | succ t =>
      cases t with
      | zero => exact markedMemoryEdgeSlotPopulationOrigin_group hZ _ history.2.1 i
      | succ t => exact ih history.2.2 t i

def markedMemoryHistoryTraceAddressGroup {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) : MarkedMemoryHistoryTraceAddress hZ history → J :=
  Sum.elim (markedMemoryPopulationGroup s)
    (fun b => markedMemoryHistoryTraceBirthGroup hZ history b.1 b.2)

@[simp] theorem markedMemoryHistoryTraceAddressGroup_birth {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (t : ℕ)
    (b : MarkedMemoryHistoryTraceBirth hZ history t) :
    markedMemoryHistoryTraceAddressGroup hZ history (Sum.inr ⟨t,b⟩) =
      (markedMemoryHistoryBirthLabel hZ history (markedMemoryTraceBirthToFinite hZ history ⟨t,b⟩)).1 := rfl

/-- Every actual chronological identity retains its group along its whole trace. -/
theorem markedMemoryHistoryTraceOrigin_group {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (t : ℕ)
    (i : MarkedMemoryPopulationIndex (markedMemoryHistoryTraceState hZ history t)) :
    markedMemoryHistoryTraceAddressGroup hZ history
      (markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ history)
        (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) t i) =
      markedMemoryPopulationGroup (markedMemoryHistoryTraceState hZ history t) i :=
  markedMemoryLineageOrigin_mark (T := MarkedMemoryHistoryTracePopulation hZ history)
    (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history)
    (fun t => markedMemoryPopulationGroup (markedMemoryHistoryTraceState hZ history t))
    (markedMemoryHistoryTraceBirthGroup hZ history) (markedMemoryHistoryTraceStep_group hZ history) t i

end
end ArtinMatthews
