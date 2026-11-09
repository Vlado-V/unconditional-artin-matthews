module

public import ArtinMatthews.MarkedMemoryActualGhostQueue
public import ArtinMatthews.MarkedMemoryActualParticles
public import ArtinMatthews.MarkedMemoryActualEdgeIncidence
public import ArtinMatthews.MarkedMemoryHistoryEdgeAccess


set_option backward.privateInPublic true
@[expose] public section

/-! Actual static particles satisfy the independent physical hit and
anchor conditions under the nonzero-weight anchor coherence consequence. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)

def markedMemoryActualPosition (v : ℕ) : Z := (markedMemoryHistoryTraceState hZ history (2*v)).1

theorem markedMemoryActualPosition_vertex (v : Fin (n+1)) :
    markedMemoryActualPosition hZ history v.val = (markedMemoryHistoryVertexState hZ history v).1 :=
  congrArg Prod.fst (markedMemoryHistoryVertexState_trace hZ history v)

theorem markedMemoryPopulationStateCast_anchor {s t : MarkedRawState P (pads+1) B Z}
    (h : s = t) (i : MarkedMemoryPopulationIndex s) :
    markedMemoryPopulationAnchor hZ t (markedMemoryPopulationStateCast h i) =
      markedMemoryPopulationAnchor hZ s i := by
  cases h
  rfl

local notation "vertex" v:max => markedMemoryHistoryVertexState hZ history v
local notation "ghost" v:max => markedMemoryHistoryVertexGhost hZ history v
local notation "target" v:max => markedMemoryGhostChoiceTarget hZ (vertex v) (ghost v)

variable (ha : MarkedMemoryHistoryAnchorAdmissible hZ history)

include ha

theorem markedMemoryActualParticle_ghost_source (v : Fin (n+1)) (j : J)
    (k : Fin ((vertex v).2.2.1.1 j : ℕ)) :
    markedMemoryActualParticle hZ history j (markedMemoryActualGhostSourceIds hZ history v j k) =
      (vertex v).2.2.2 j k := by
  apply markedMemoryForgetBandParticle_injective
  exact (markedMemoryHistoryTraceOrigin_anchor hZ history ha ((markedMemoryHistoryGhostTime n v))
    (markedMemoryHistoryGhostSourceIndex hZ history v (Sum.inr ⟨j,k⟩))).trans
      (markedMemoryPopulationStateCast_anchor hZ
        (markedMemoryHistoryTraceState_stage hZ history (markedMemoryHistoryVertexStage n v)).symm (Sum.inr ⟨j,k⟩))

theorem markedMemoryActualParticle_ghost_target (v : Fin (n+1)) (j : J)
    (k : Fin ((target v).2.2.1.1 j : ℕ)) :
    markedMemoryActualParticle hZ history j (markedMemoryActualGhostTargetIds hZ history v j k) =
      (target v).2.2.2 j k := by
  apply markedMemoryForgetBandParticle_injective
  exact (markedMemoryHistoryTraceOrigin_anchor hZ history ha ((markedMemoryHistoryGhostTime n v)+1)
    (markedMemoryHistoryGhostTargetIndex hZ history v (Sum.inr ⟨j,k⟩))).trans
      (markedMemoryPopulationStateCast_anchor hZ (markedMemoryHistoryGhostTarget_trace hZ history v).symm (Sum.inr ⟨j,k⟩))

theorem markedMemoryActualParticle_ghost_birth (v : Fin (n+1)) (j : J)
    (k : Fin ((ghost v).sizes.1 j : ℕ)) :
    markedMemoryActualParticle hZ history j (markedMemoryActualGhostBirthIds hZ history v j k) =
      markedRawAnchoredParticle (P j) ((ghost v).births j k) (vertex v).1.1 (hZ _ (vertex v).1.2) := by
  exact (markedMemoryActualParticle_ghost_target hZ history ha v j
    ((markedMemoryGhostOrigin (vertex v).2.2 (ghost v).deletion (ghost v).sizes j).symm (Sum.inr k))).trans
      (markedMemoryGhostOrigin_birth (vertex v).2.2 (vertex v).1.1 (hZ _ (vertex v).1.2)
        (ghost v).deletion (ghost v).sizes (ghost v).births j k)

theorem markedMemoryActual_ghost_death_hit (v : ℕ) (hv : v ≤ n) (j : J)
    (a : MarkedMemoryActualFiber hZ history j)
    (hf : markedMemoryActualFirst hZ history j a ≤ 2*v)
    (hl : markedMemoryActualLast hZ history j a = 2*v)
    (hn : ¬ markedMemoryActualActive hZ history (2*v) j a) :
    MarkedRawParticleHits (P j) (markedMemoryActualPosition hZ history v).1
      (hZ _ (markedMemoryActualPosition hZ history v).2) (markedMemoryActualParticle hZ history j a) := by
  let w : Fin (n+1) := ⟨v,by omega⟩
  have ht : (markedMemoryHistoryGhostTime n w) = 2*v := markedMemoryHistoryGhostTime_eq n w
  have hm : a ∈ markedMemoryActualPendingQueue hZ history ((markedMemoryHistoryGhostTime n w)) j :=
    (markedMemoryActualPendingQueue_interval hZ history ((markedMemoryHistoryGhostTime n w)) (by rw [ht]; omega) j a).mpr
      ⟨by simpa only [ht] using hf,by simpa only [ht] using hl.ge,by simpa only [ht] using hn⟩
  have hm' : a ∈ List.ofFn (markedMemoryActualGhostSourceIds hZ history w j) := by
    simpa only [markedMemoryActualGhostSourceIds_list] using hm
  obtain ⟨k,hk⟩ := List.mem_ofFn.mp hm'
  have hlast := (congrArg (markedMemoryActualLast hZ history j) hk).trans hl
  have hd := (markedMemoryActualGhost_deleted_iff hZ history w j k).mpr (by simpa only [ht] using hlast)
  have hh := (Finset.mem_filter.mp ((ghost w).allowed j hd)).2
  have hparticle := (congrArg (markedMemoryActualParticle hZ history j) hk).symm.trans
    (markedMemoryActualParticle_ghost_source hZ history ha w j k)
  rw [hparticle]
  have hz : markedMemoryActualPosition hZ history v = (vertex w).1 := markedMemoryActualPosition_vertex hZ history w
  simpa only [hz] using hh

theorem markedMemoryActual_ghost_birth_anchor (v : ℕ) (hv : v ≤ n) (j : J)
    (a : MarkedMemoryActualFiber hZ history j) (hb : a ∈ markedMemoryActualBirthQueue hZ history (2*v) j) :
    markedMemoryActualParticle hZ history j a = markedRawAnchoredParticle (P j)
      (markedMemoryActualParticle hZ history j a).1 (markedMemoryActualPosition hZ history v).1
        (hZ _ (markedMemoryActualPosition hZ history v).2) := by
  let w : Fin (n+1) := ⟨v,by omega⟩
  have ht : (markedMemoryHistoryGhostTime n w) = 2*v := markedMemoryHistoryGhostTime_eq n w
  rw [← ht,markedMemoryActualGhost_birthQueue] at hb
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hb
  rw [markedMemoryActualParticle_ghost_birth hZ history ha]
  have hz : markedMemoryActualPosition hZ history v = (vertex w).1 := markedMemoryActualPosition_vertex hZ history w
  exact congrArg (fun z : Z => markedRawAnchoredParticle (P j) ((ghost w).births j k) z.1 (hZ _ z.2)) hz.symm

theorem markedMemoryActual_incoming_hit (v : Fin n) (j : J) :
    MarkedRawParticleHits (P j) (markedMemoryActualPosition hZ history (v.val+1)).1
      (hZ _ (markedMemoryActualPosition hZ history (v.val+1)).2)
      (markedMemoryActualParticle hZ history j (markedMemoryActualIncoming hZ history v j)) := by
  unfold markedMemoryActualIncoming
  rw [markedMemoryActualParticle_active hZ history ha]
  have ht : (2*v.val+1)+1 = 2*(v.val+1) := by omega
  rw [ht]
  rfl

theorem markedMemoryActual_outgoing_anchor (v : Fin n) (j : J) :
    markedMemoryActualParticle hZ history j (markedMemoryActualOutgoing hZ history v j) =
      markedRawAnchoredParticle (P j)
        (markedMemoryActualParticle hZ history j (markedMemoryActualOutgoing hZ history v j)).1
        (markedMemoryActualPosition hZ history v.val).1 (hZ _ (markedMemoryActualPosition hZ history v.val).2) := by
  unfold markedMemoryActualOutgoing
  rw [markedMemoryActualParticle_active hZ history ha]
  have hp : (markedMemoryHistoryTraceState hZ history (2*v.val+1)).1 = markedMemoryActualPosition hZ history v.val := by
    rw [markedMemoryHistoryEdgeSource_trace]
    exact (markedMemoryActualPosition_vertex hZ history v.castSucc).symm
  exact congrArg (fun z : Z => markedRawAnchoredParticle (P j)
    ((markedMemoryHistoryTraceState hZ history (2*v.val+1)).2.1 j
      ((markedMemoryHistoryVertexEdge hZ history v).1 j (Fin.last pads))) z.1 (hZ _ z.2)) hp

end
end ArtinMatthews
