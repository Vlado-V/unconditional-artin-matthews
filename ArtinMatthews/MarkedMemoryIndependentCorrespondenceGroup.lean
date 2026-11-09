module

public import ArtinMatthews.MarkedMemoryIndependentCorrespondence
public import ArtinMatthews.MarkedMemoryHistoryGroups


set_option backward.privateInPublic true
@[expose] public section

/-! The constructed identity equivalence also preserves the actual band,
without deducing it from numeric prime distinctness. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)}

theorem markedMemoryPopulationStateCast_group {s t : MarkedRawState P (pads+1) B Z}
    (h : s = t) (i : MarkedMemoryPopulationIndex s) :
    markedMemoryPopulationGroup t (markedMemoryPopulationStateCast h i) = markedMemoryPopulationGroup s i := by
  cases h
  rfl

variable {A : J → Type*} [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)]
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {n : ℕ}
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (order : Fin n → J → Equiv.Perm (Fin pads))

theorem markedMemoryIndependentPopulationLabel_group (t : ℕ) (ht : t ≤ 2*n+1)
    (i : MarkedMemoryPopulationIndex (markedMemoryIndependentStageState hZ d t ht)) :
    (markedMemoryIndependentPopulationLabel hZ d t ht i).1 =
      markedMemoryPopulationGroup (markedMemoryIndependentStageState hZ d t ht) i := by
  rcases i with ⟨j,k⟩ | ⟨j,k⟩ <;> rfl

theorem markedMemoryIndependentTraceIds_group (t : ℕ) (ht : t ≤ 2*n+1)
    (i : MarkedMemoryPopulationIndex (markedMemoryHistoryTraceState hZ (markedMemoryIndependentHistory hZ d order) t)) :
    (markedMemoryIndependentTraceIds hZ d order t ht i).1 =
      markedMemoryPopulationGroup (markedMemoryHistoryTraceState hZ (markedMemoryIndependentHistory hZ d order) t) i :=
  (markedMemoryIndependentPopulationLabel_group hZ d t ht
    (markedMemoryPopulationStateCast (markedMemoryIndependentHistory_trace_state hZ d order t ht) i)).trans
      (markedMemoryPopulationStateCast_group (markedMemoryIndependentHistory_trace_state hZ d order t ht) i)

theorem markedMemoryIndependentAddress_group
    (a : MarkedMemoryHistoryTraceAddress hZ (markedMemoryIndependentHistory hZ d order)) :
    (markedMemoryIndependentAddressEquiv hZ d order a).1 =
      markedMemoryHistoryTraceAddressGroup hZ (markedMemoryIndependentHistory hZ d order) a := by
  obtain ⟨t,ht,i,hi⟩ := markedMemoryHistoryTraceAddress_present hZ (markedMemoryIndependentHistory hZ d order) a
  have hl := (congrArg (markedMemoryIndependentAddressEquiv hZ d order) hi).symm.trans
    (markedMemoryIndependentAddress_origin hZ d order t ht i)
  have hg := markedMemoryHistoryTraceOrigin_group hZ (markedMemoryIndependentHistory hZ d order) t i
  rw [hi] at hg
  exact (congrArg Sigma.fst hl).trans ((markedMemoryIndependentTraceIds_group hZ d order t ht i).trans hg.symm)

theorem markedMemoryIndependentTraceIds_pending (t : ℕ) (ht : t ≤ 2*n+1) (j : J)
    (k : Fin ((markedMemoryHistoryTraceState hZ (markedMemoryIndependentHistory hZ d order) t).2.2.1.1 j : ℕ)) :
    markedMemoryIndependentTraceIds hZ d order t ht (Sum.inr ⟨j,k⟩) =
      ⟨j,(markedMemoryIndependentQueue hZ d t j).get
        (Fin.cast (congrArg (fun r : MarkedRawState P (pads+1) B Z => (r.2.2.1.1 j : ℕ))
          (markedMemoryIndependentHistory_trace_state hZ d order t ht)) k)⟩ :=
  congrArg (markedMemoryIndependentPopulationLabel hZ d t ht)
    (markedMemoryPopulationStateCast_pending (markedMemoryIndependentHistory_trace_state hZ d order t ht) j k)

theorem markedMemoryIndependentAddress_active_slot (t : ℕ) (ht : t ≤ 2*n+1) (j : J) (k : Fin (pads+1)) :
    markedMemoryIndependentAddressEquiv hZ d order
      (markedMemoryLineageOrigin (markedMemoryHistoryTraceStep hZ (markedMemoryIndependentHistory hZ d order)) t (Sum.inl ⟨j,k⟩)) =
        ⟨j,d.activeId (t/2) j k⟩ :=
  (markedMemoryIndependentAddress_origin hZ d order t ht (Sum.inl ⟨j,k⟩)).trans
    (markedMemoryIndependentTraceIds_active hZ d order t ht j k)

theorem markedMemoryIndependentAddress_pending_slot (t : ℕ) (ht : t ≤ 2*n+1) (j : J)
    (k : Fin ((markedMemoryHistoryTraceState hZ (markedMemoryIndependentHistory hZ d order) t).2.2.1.1 j : ℕ)) :
    markedMemoryIndependentAddressEquiv hZ d order
      (markedMemoryLineageOrigin (markedMemoryHistoryTraceStep hZ (markedMemoryIndependentHistory hZ d order)) t (Sum.inr ⟨j,k⟩)) =
        ⟨j,(markedMemoryIndependentQueue hZ d t j).get
          (Fin.cast (congrArg (fun r : MarkedRawState P (pads+1) B Z => (r.2.2.1.1 j : ℕ))
            (markedMemoryIndependentHistory_trace_state hZ d order t ht)) k)⟩ :=
  (markedMemoryIndependentAddress_origin hZ d order t ht (Sum.inr ⟨j,k⟩)).trans
    (markedMemoryIndependentTraceIds_pending hZ d order t ht j k)

theorem markedMemoryIndependentAddress_birth_slot (t : ℕ) (ht : t < 2*n+1)
    (b : MarkedMemoryHistoryTraceBirth hZ (markedMemoryIndependentHistory hZ d order) t) :
    markedMemoryIndependentAddressEquiv hZ d order (Sum.inr ⟨t,b⟩) =
      markedMemoryIndependentTraceBirthLabel hZ d order t ht b := rfl

end
end ArtinMatthews
