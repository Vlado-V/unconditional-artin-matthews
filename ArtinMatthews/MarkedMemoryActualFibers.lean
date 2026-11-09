module

public import ArtinMatthews.MarkedMemoryHistoryRunWeight
public import ArtinMatthews.MarkedMemoryHistoryGroups
public import ArtinMatthews.MarkedMemoryLifespanQueueSchedule


set_option backward.privateInPublic true
@[expose] public section

/-! Canonical independent identity sets extracted from an actual trace.
Each band contains the actual lineage addresses in that band; active and
pending labels retain their literal slot order. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)

abbrev MarkedMemoryActualFiber (j : J) :=
  {a : MarkedMemoryHistoryTraceAddress hZ history // markedMemoryHistoryTraceAddressGroup hZ history a = j}

instance markedMemoryActualFiber_fintype (j : J) : Fintype (MarkedMemoryActualFiber hZ history j) := by
  classical
  infer_instance

def markedMemoryActualFiberEquiv : (Σ j, MarkedMemoryActualFiber hZ history j) ≃ MarkedMemoryHistoryTraceAddress hZ history where
  toFun a := a.2.1
  invFun a := ⟨markedMemoryHistoryTraceAddressGroup hZ history a,⟨a,rfl⟩⟩
  left_inv a := by rcases a with ⟨j,a,h⟩; cases h; rfl
  right_inv _ := rfl

def markedMemoryActualFirst (j : J) (a : MarkedMemoryActualFiber hZ history j) : ℕ :=
  markedMemoryLineageBirthTime a.1

def markedMemoryActualLast (j : J) (a : MarkedMemoryActualFiber hZ history j) : ℕ :=
  markedMemoryHistoryLifespanLast hZ history a.1

def markedMemoryActualOrigin (t : ℕ) :
    MarkedMemoryHistoryTracePopulation hZ history t ↪ MarkedMemoryHistoryTraceAddress hZ history where
  toFun := markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ history)
    (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) t
  inj' := markedMemoryLineageOrigin_injective (T := MarkedMemoryHistoryTracePopulation hZ history)
    (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) t

omit [DecidableEq J] in
theorem markedMemoryActualOrigin_injective (t : ℕ) :
    Function.Injective (markedMemoryLineageOrigin
      (T := MarkedMemoryHistoryTracePopulation hZ history) (Birth := MarkedMemoryHistoryTraceBirth hZ history)
      (markedMemoryHistoryTraceStep hZ history) t) :=
  markedMemoryLineageOrigin_injective (T := MarkedMemoryHistoryTracePopulation hZ history)
    (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) t

def markedMemoryActualActiveIds (t : ℕ) (j : J) : Fin (pads+1) ↪ MarkedMemoryActualFiber hZ history j where
  toFun k := ⟨markedMemoryActualOrigin hZ history t (Sum.inl ⟨j,k⟩),
    markedMemoryHistoryTraceOrigin_group hZ history t (Sum.inl ⟨j,k⟩)⟩
  inj' := by
    intro a b hab
    have hh := congrArg Subtype.val hab
    change markedMemoryActualOrigin hZ history t (Sum.inl ⟨j,a⟩) =
      markedMemoryActualOrigin hZ history t (Sum.inl ⟨j,b⟩) at hh
    have h := (markedMemoryActualOrigin hZ history t).injective hh
    cases h
    rfl

def markedMemoryActualPendingIds (t : ℕ) (j : J) :
    Fin ((markedMemoryHistoryTraceState hZ history t).2.2.1.1 j : ℕ) ↪ MarkedMemoryActualFiber hZ history j where
  toFun k := ⟨markedMemoryActualOrigin hZ history t (Sum.inr ⟨j,k⟩),
    markedMemoryHistoryTraceOrigin_group hZ history t (Sum.inr ⟨j,k⟩)⟩
  inj' := by
    intro a b hab
    have hh := congrArg Subtype.val hab
    change markedMemoryActualOrigin hZ history t (Sum.inr ⟨j,a⟩) =
      markedMemoryActualOrigin hZ history t (Sum.inr ⟨j,b⟩) at hh
    have h := (markedMemoryActualOrigin hZ history t).injective hh
    cases h
    rfl

def markedMemoryActualActive (t : ℕ) (j : J) (a : MarkedMemoryActualFiber hZ history j) : Prop :=
  ∃ k, markedMemoryActualActiveIds hZ history t j k = a

def markedMemoryActualPendingQueue (t : ℕ) (j : J) : List (MarkedMemoryActualFiber hZ history j) :=
  List.ofFn (markedMemoryActualPendingIds hZ history t j)

omit [DecidableEq J] in
theorem markedMemoryActualPendingQueue_nodup (t : ℕ) (j : J) :
    (markedMemoryActualPendingQueue hZ history t j).Nodup :=
  List.nodup_ofFn_ofInjective (markedMemoryActualPendingIds hZ history t j).injective

omit [DecidableEq J] in
theorem markedMemoryActualPendingQueue_length (t : ℕ) (j : J) :
    (markedMemoryActualPendingQueue hZ history t j).length =
      ((markedMemoryHistoryTraceState hZ history t).2.2.1.1 j : ℕ) := List.length_ofFn

omit [DecidableEq J] in
theorem markedMemoryActualActive_not_pending (t : ℕ) (j : J) (k : Fin (pads+1)) :
    markedMemoryActualActiveIds hZ history t j k ∉ markedMemoryActualPendingQueue hZ history t j := by
  rw [markedMemoryActualPendingQueue, List.mem_ofFn]
  rintro ⟨l,hl⟩
  have hh := congrArg Subtype.val hl
  change markedMemoryActualOrigin hZ history t (Sum.inr ⟨j,l⟩) =
    markedMemoryActualOrigin hZ history t (Sum.inl ⟨j,k⟩) at hh
  have h := (markedMemoryActualOrigin hZ history t).injective hh
  cases h

omit [DecidableEq J] in
theorem markedMemoryActualPendingQueue_mem (t : ℕ) (j : J) (a : MarkedMemoryActualFiber hZ history j) :
    a ∈ markedMemoryActualPendingQueue hZ history t j ↔
      MarkedMemoryLineagePresent (markedMemoryHistoryTraceStep hZ history) t a.1 ∧
        ¬ markedMemoryActualActive hZ history t j a := by
  constructor
  · rw [markedMemoryActualPendingQueue, List.mem_ofFn]
    rintro ⟨k,rfl⟩
    refine ⟨⟨Sum.inr ⟨j,k⟩,rfl⟩,?_⟩
    rintro ⟨l,hl⟩
    exact markedMemoryActualActive_not_pending hZ history t j l
      (by rw [hl]; exact List.mem_ofFn.mpr ⟨k,rfl⟩)
  · rintro ⟨⟨x,hx⟩,ha⟩
    have hg : markedMemoryPopulationGroup (markedMemoryHistoryTraceState hZ history t) x = j :=
      (markedMemoryHistoryTraceOrigin_group hZ history t x).symm.trans
        ((congrArg (markedMemoryHistoryTraceAddressGroup hZ history) hx).trans a.2)
    rcases x with ⟨k,l⟩ | ⟨k,l⟩
    · change k = j at hg
      subst k
      exact False.elim (ha ⟨l,Subtype.ext hx⟩)
    · change k = j at hg
      subst k
      exact List.mem_ofFn.mpr ⟨l,Subtype.ext hx⟩

omit [DecidableEq J] in
theorem markedMemoryActualPendingQueue_interval (t : ℕ) (ht : t ≤ 2*n+1) (j : J)
    (a : MarkedMemoryActualFiber hZ history j) :
    a ∈ markedMemoryActualPendingQueue hZ history t j ↔
      markedMemoryActualFirst hZ history j a ≤ t ∧ t ≤ markedMemoryActualLast hZ history j a ∧
        ¬ markedMemoryActualActive hZ history t j a := by
  rw [markedMemoryActualPendingQueue_mem]
  have hp := markedMemoryHistory_lifespan_exact hZ history a.1 t
  constructor
  · rintro ⟨ha,hn⟩
    have hh := hp.mp ⟨ht,ha⟩
    exact ⟨hh.1,hh.2,hn⟩
  · rintro ⟨hf,hl,hn⟩
    exact ⟨(hp.mpr ⟨hf,hl⟩).2,hn⟩

omit [DecidableEq J] in
theorem markedMemoryActual_bounds (j : J) (a : MarkedMemoryActualFiber hZ history j) :
    markedMemoryActualFirst hZ history j a ≤ markedMemoryActualLast hZ history j a ∧
      markedMemoryActualLast hZ history j a ≤ 2*n+1 :=
  markedMemoryHistory_lifespan_bounds hZ history a.1

end
end ArtinMatthews
