module

public import ArtinMatthews.MarkedMemoryActualFibers
public import ArtinMatthews.MarkedMemoryHistoryEdgeAccess
public import ArtinMatthews.MarkedMemoryCopiedActiveExchange
public import ArtinMatthews.MarkedMemoryLabelTransport
public import ArtinMatthews.MarkedMemoryPopulationTransport
public import ArtinMatthews.MarkedMemoryHistoryEventKinds


set_option backward.privateInPublic true
@[expose] public section

/-! The actual edge's source and target identities, read through its
literal slot permutations. Copies give the active exchange law, and the
incoming identity cannot be any old active identity. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s) (v : Fin n)

local notation "edge" => markedMemoryHistoryVertexEdge hZ history v
local notation "source" => markedMemoryGhostChoiceTarget hZ
  (markedMemoryHistoryVertexState hZ history v.castSucc) (markedMemoryHistoryVertexGhost hZ history v.castSucc)
local notation "target" => markedMemoryEdgeChoiceTarget hZ source edge
local notation "time" => 2*v.val+1

theorem markedMemoryActualEdgeTarget_trace :
    markedMemoryHistoryTraceState hZ history (time+1) = target :=
  (congrArg (markedMemoryHistoryTraceState hZ history) (show time+1 = 2*(v.val+1) by omega)).trans
    (markedMemoryHistoryEdgeTarget_trace hZ history v)

def markedMemoryActualEdgeSourceOrigin : MarkedMemoryPopulationIndex source ↪ MarkedMemoryHistoryTraceAddress hZ history :=
  (markedMemoryPopulationStateCast (markedMemoryHistoryEdgeSource_trace hZ history v).symm).toEmbedding.trans
    (markedMemoryActualOrigin hZ history time)

def markedMemoryActualEdgeTargetOrigin : MarkedMemoryPopulationIndex target ↪ MarkedMemoryHistoryTraceAddress hZ history :=
  (markedMemoryPopulationStateCast (markedMemoryActualEdgeTarget_trace hZ history v).symm).toEmbedding.trans
    (markedMemoryActualOrigin hZ history (time+1))

def markedMemoryActualEdgeBirthOrigin (b : MarkedMemoryEdgeBirthIndex edge) : MarkedMemoryHistoryTraceAddress hZ history :=
  Sum.inr ⟨time,cast (markedMemoryHistoryVertexEdge_birthType hZ history v).symm b⟩

theorem markedMemoryActualEdgeOrigin (i : MarkedMemoryPopulationIndex target) :
    Sum.elim (markedMemoryActualEdgeSourceOrigin hZ history v) (markedMemoryActualEdgeBirthOrigin hZ history v)
      (markedMemoryEdgeSlotPopulationOrigin hZ source edge i) = markedMemoryActualEdgeTargetOrigin hZ history v i :=
  markedMemorySumLabel_transport
    (congrArg MarkedMemoryPopulationIndex (markedMemoryActualEdgeTarget_trace hZ history v).symm)
    (congrArg MarkedMemoryPopulationIndex (markedMemoryHistoryEdgeSource_trace hZ history v).symm)
    (markedMemoryHistoryVertexEdge_birthType hZ history v).symm
    (markedMemoryEdgeSlotPopulationOrigin hZ source edge) (markedMemoryHistoryTraceStep hZ history time)
    (markedMemoryHistoryVertexEdge_step hZ history v).symm
    (markedMemoryActualOrigin hZ history time) (fun b => Sum.inr ⟨time,b⟩)
    (markedMemoryActualOrigin hZ history (time+1)) (fun _ => rfl) i

theorem markedMemoryActualEdgeSourceOrigin_active (j : J) (k : Fin (pads+1)) :
    markedMemoryActualEdgeSourceOrigin hZ history v (Sum.inl ⟨j,k⟩) =
      markedMemoryActualOrigin hZ history time (Sum.inl ⟨j,k⟩) :=
  congrArg (markedMemoryActualOrigin hZ history time)
    (markedMemoryPopulationStateCast_active (markedMemoryHistoryEdgeSource_trace hZ history v).symm j k)

theorem markedMemoryActualEdgeTargetOrigin_active (j : J) (k : Fin (pads+1)) :
    markedMemoryActualEdgeTargetOrigin hZ history v (Sum.inl ⟨j,k⟩) =
      markedMemoryActualOrigin hZ history (time+1) (Sum.inl ⟨j,k⟩) :=
  congrArg (markedMemoryActualOrigin hZ history (time+1))
    (markedMemoryPopulationStateCast_active (markedMemoryActualEdgeTarget_trace hZ history v).symm j k)

def markedMemoryActualOutgoing (j : J) : MarkedMemoryActualFiber hZ history j :=
  markedMemoryActualActiveIds hZ history time j (edge.1 j (Fin.last pads))

def markedMemoryActualIncoming (j : J) : MarkedMemoryActualFiber hZ history j :=
  markedMemoryActualActiveIds hZ history (time+1) j ((edge.2.2 j).symm (Fin.last pads))

theorem markedMemoryActualEdge_copied (j : J) (k : Fin pads) :
    markedMemoryActualActiveIds hZ history time j (edge.1 j k.castSucc) =
      markedMemoryActualActiveIds hZ history (time+1) j ((edge.2.2 j).symm k.castSucc) := by
  apply Subtype.ext
  have h := markedMemoryActualEdgeOrigin hZ history v (Sum.inl ⟨j,(edge.2.2 j).symm k.castSucc⟩)
  have hc := congrArg (Sum.elim (markedMemoryActualEdgeSourceOrigin hZ history v)
    (markedMemoryActualEdgeBirthOrigin hZ history v)) (markedMemoryEdgeSlotOrigin_copied_index hZ source edge j k)
  exact (markedMemoryActualEdgeSourceOrigin_active hZ history v j (edge.1 j k.castSucc)).symm.trans
    ((hc.symm.trans h).trans (markedMemoryActualEdgeTargetOrigin_active hZ history v j ((edge.2.2 j).symm k.castSucc)))

theorem markedMemoryActualEdge_exchange (j : J) (a : MarkedMemoryActualFiber hZ history j) :
    markedMemoryActualActive hZ history (time+1) j a ↔
      (markedMemoryActualActive hZ history time j a ∧ a ≠ markedMemoryActualOutgoing hZ history v j) ∨
        a = markedMemoryActualIncoming hZ history v j :=
  markedMemoryCopiedActive_exchange (markedMemoryActualActiveIds hZ history time j)
    (markedMemoryActualActiveIds hZ history (time+1) j) (edge.1 j) (edge.2.2 j)
    (markedMemoryActualEdge_copied hZ history v j) a

theorem markedMemoryActualIncoming_not_old_active (j : J) (k₀ : Fin (pads+1)) :
    markedMemoryActualIncoming hZ history v j ≠ markedMemoryActualActiveIds hZ history time j k₀ := by
  intro heq
  have hv := congrArg Subtype.val heq
  have hs : markedMemoryActualEdgeTargetOrigin hZ history v (Sum.inl ⟨j,(edge.2.2 j).symm (Fin.last pads)⟩) =
      markedMemoryActualEdgeSourceOrigin hZ history v (Sum.inl ⟨j,k₀⟩) :=
    (markedMemoryActualEdgeTargetOrigin_active hZ history v j _).trans
      (hv.trans (markedMemoryActualEdgeSourceOrigin_active hZ history v j k₀).symm)
  have ho := markedMemoryActualEdgeOrigin hZ history v (Sum.inl ⟨j,(edge.2.2 j).symm (Fin.last pads)⟩)
  by_cases hp : edge.2.1.promotions j = none
  · have hf := congrArg (Sum.elim (markedMemoryActualEdgeSourceOrigin hZ history v)
      (markedMemoryActualEdgeBirthOrigin hZ history v)) (markedMemoryEdgeSlotOrigin_fresh hZ source edge ⟨j,hp⟩)
    have he : markedMemoryActualEdgeSourceOrigin hZ history v (Sum.inl ⟨j,k₀⟩) =
        markedMemoryActualEdgeBirthOrigin hZ history v ⟨j,hp⟩ := hs.symm.trans (ho.symm.trans hf)
    have hfirst := markedMemoryLineageOrigin_birthTime_le
      (T := MarkedMemoryHistoryTracePopulation hZ history) (Birth := MarkedMemoryHistoryTraceBirth hZ history)
      (markedMemoryHistoryTraceStep hZ history) time (Sum.inl ⟨j,k₀⟩)
    have hb := congrArg markedMemoryLineageBirthTime he
    rw [markedMemoryActualEdgeSourceOrigin_active] at hb
    change markedMemoryLineageBirthTime (markedMemoryActualOrigin hZ history time (Sum.inl ⟨j,k₀⟩)) = time+1 at hb
    change markedMemoryLineageBirthTime (markedMemoryActualOrigin hZ history time (Sum.inl ⟨j,k₀⟩)) ≤ time at hfirst
    omega
  · obtain ⟨k,hk⟩ := Option.ne_none_iff_exists'.mp hp
    have hf := congrArg (Sum.elim (markedMemoryActualEdgeSourceOrigin hZ history v)
      (markedMemoryActualEdgeBirthOrigin hZ history v)) (markedMemoryEdgeSlotOrigin_last_some hZ source edge j k hk)
    have he : markedMemoryActualEdgeSourceOrigin hZ history v (Sum.inr ⟨j,k⟩) =
        markedMemoryActualEdgeSourceOrigin hZ history v (Sum.inl ⟨j,k₀⟩) := (ho.symm.trans hf).symm.trans hs
    have hh := (markedMemoryActualEdgeSourceOrigin hZ history v).injective he
    cases hh

theorem markedMemoryActualEdge_distinct (j : J) :
    markedMemoryActualIncoming hZ history v j ≠ markedMemoryActualOutgoing hZ history v j :=
  markedMemoryActualIncoming_not_old_active hZ history v j (edge.1 j (Fin.last pads))

end
end ArtinMatthews
