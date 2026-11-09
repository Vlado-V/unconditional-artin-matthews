module

public import ArtinMatthews.MarkedMemoryActualGhostTrace
public import ArtinMatthews.MarkedMemoryActualEdgeIncidence


set_option backward.privateInPublic true
@[expose] public section

/-! The actual trace provides an independent interval-and-incidence
schedule. All local lifespan axioms follow from the performed choices. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)

theorem markedMemoryActualOddIndex (t : ℕ) (ht : t < 2*n+1) (ho : t % 2 = 1) :
    ∃ v : Fin n, t = 2*v.val+1 := by
  refine ⟨⟨t/2,by omega⟩,?_⟩
  change t = 2*(t/2)+1
  omega

def markedMemoryActualQueueData (j : J) :
    MarkedMemoryQueueLifespanData (MarkedMemoryActualFiber hZ history j) (2*n+1) where
  first := markedMemoryActualFirst hZ history j
  last := markedMemoryActualLast hZ history j
  active := fun t => markedMemoryActualActive hZ history t j
  initial := markedMemoryActualPendingQueue hZ history 0 j
  births := fun t => markedMemoryActualBirthQueue hZ history t j
  incoming := fun t => markedMemoryActualIncomingAt hZ history t j
  outgoing := fun t => markedMemoryActualOutgoingAt hZ history t j
  nonempty := fun a => (markedMemoryActual_bounds hZ history j a).1
  bounded := fun a => (markedMemoryActual_bounds hZ history j a).2
  initial_nodup := markedMemoryActualPendingQueue_nodup hZ history 0 j
  initial_mem := markedMemoryActualPendingQueue_interval hZ history 0 (by omega) j
  ghost_active := fun t _ he => markedMemoryActualActive_ghost hZ history t he j
  ghost_births := fun t ht he => markedMemoryActualBirthQueue_mem hZ history t ht he j
  ghost_nodup := fun t _ _ => markedMemoryActualBirthQueue_nodup hZ history t j
  edge_distinct := by
    intro t ht ho
    obtain ⟨v,rfl⟩ := markedMemoryActualOddIndex t ht ho
    rw [markedMemoryActualIncomingAt_edge,markedMemoryActualOutgoingAt_edge]
    exact markedMemoryActualEdge_distinct hZ history v j
  edge_outgoing_active := by
    intro t ht ho
    obtain ⟨v,rfl⟩ := markedMemoryActualOddIndex t ht ho
    rw [markedMemoryActualOutgoingAt_edge]
    exact ⟨_,rfl⟩
  edge_outgoing_alive := by
    intro t ht ho
    obtain ⟨v,rfl⟩ := markedMemoryActualOddIndex t ht ho
    rw [markedMemoryActualOutgoingAt_edge]
    exact (markedMemoryHistory_lifespan_exact hZ history _ (2*v.val+1)).mp
      ⟨by omega,Sum.inl ⟨j,(markedMemoryHistoryVertexEdge hZ history v).1 j (Fin.last pads)⟩,rfl⟩
  edge_active := by
    intro t ht ho a
    obtain ⟨v,rfl⟩ := markedMemoryActualOddIndex t ht ho
    rw [markedMemoryActualIncomingAt_edge,markedMemoryActualOutgoingAt_edge]
    exact markedMemoryActualEdge_exchange hZ history v j a
  edge_births := by
    intro t ht ho a hb
    obtain ⟨v,rfl⟩ := markedMemoryActualOddIndex t ht ho
    rw [markedMemoryActualIncomingAt_edge]
    exact markedMemoryActualEdge_birth hZ history v j a hb
  edge_deaths := by
    intro t ht ho a hl
    obtain ⟨v,rfl⟩ := markedMemoryActualOddIndex t ht ho
    rw [markedMemoryActualOutgoingAt_edge]
    exact markedMemoryActualEdge_death hZ history v j a hl

/-- At every time the reconstructed queue has exactly the actual pending
identities. The order comparison is proved separately. -/
theorem markedMemoryActualQueueData_mem (t : ℕ) (ht : t ≤ 2*n+1) (j : J)
    (a : MarkedMemoryActualFiber hZ history j) :
    a ∈ markedMemoryPendingQueueAt (markedMemoryActualQueueData hZ history j) t ↔
      a ∈ markedMemoryActualPendingQueue hZ history t j :=
  (markedMemoryPendingQueueAt_mem _ t ht a).trans
    (markedMemoryActualPendingQueue_interval hZ history t ht j a).symm

end
end ArtinMatthews
