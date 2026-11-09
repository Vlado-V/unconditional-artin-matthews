module

public import ArtinMatthews.MarkedMemoryIndependentBirths
public import ArtinMatthews.MarkedMemoryGhostQueueLabels


set_option backward.privateInPublic true
@[expose] public section

/-! The independent vertex and post-ghost label functions are the
transported finite-population embeddings. The actual reconstructed ghost
preserves these labels, including every ordered performed birth. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {n : ℕ}
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

def markedMemoryIndependentVertexValue (v : ℕ) (hv : v ≤ n) :
    MarkedMemoryPopulationIndex (markedMemoryIndependentState hZ d v hv) → Σ j, A j :=
  markedMemoryGhostQueueSourceLabel (d.position v) (fun j k => (d.particle j (d.activeId v j k)).1)
    (fun j k => d.activeId v j k) (markedMemoryIndependentQueue hZ d (2*v)) d.particle
    (markedMemoryIndependentQueue_bound hZ d (2*v) (by omega))

def markedMemoryIndependentPostGhostValue (v : ℕ) (hv : v ≤ n) :
    MarkedMemoryPopulationIndex (markedMemoryIndependentPostGhost hZ d v hv) → Σ j, A j :=
  markedMemoryGhostQueueSourceLabel (d.position v) (fun j k => (d.particle j (d.activeId v j k)).1)
    (fun j k => d.activeId v j k) (markedMemoryIndependentQueue hZ d (2*v+1)) d.particle
    (markedMemoryIndependentQueue_bound hZ d (2*v+1) (by omega))

theorem markedMemoryIndependentVertexValue_stage (v : ℕ) (hv : v ≤ n)
    (i : MarkedMemoryPopulationIndex (markedMemoryIndependentState hZ d v hv)) :
    markedMemoryIndependentPopulationLabel hZ d (2*v) (by omega)
      (markedMemoryPopulationStateCast (markedMemoryIndependentStageState_even hZ d v hv).symm i) =
        markedMemoryIndependentVertexValue hZ d v hv i := by
  rcases i with ⟨j,k⟩ | ⟨j,k⟩
  · rw [markedMemoryPopulationStateCast_active]
    change (⟨j,d.activeId ((2*v)/2) j k⟩ : Σ j, A j) = ⟨j,d.activeId v j k⟩
    have he : (2*v)/2 = v := by omega
    rw [he]
  · rw [markedMemoryPopulationStateCast_pending]
    change (⟨j,(markedMemoryIndependentQueue hZ d (2*v) j).get (Fin.cast (by rfl) k)⟩ : Σ j, A j) =
      ⟨j,(markedMemoryIndependentQueue hZ d (2*v) j).get k⟩
    exact congrArg (fun k => (⟨j,(markedMemoryIndependentQueue hZ d (2*v) j).get k⟩ : Σ j, A j)) (Fin.ext rfl)

theorem markedMemoryIndependentPostGhostValue_stage (v : ℕ) (hv : v ≤ n)
    (i : MarkedMemoryPopulationIndex (markedMemoryIndependentPostGhost hZ d v hv)) :
    markedMemoryIndependentPopulationLabel hZ d (2*v+1) (by omega)
      (markedMemoryPopulationStateCast (markedMemoryIndependentStageState_odd hZ d v hv).symm i) =
        markedMemoryIndependentPostGhostValue hZ d v hv i := by
  rcases i with ⟨j,k⟩ | ⟨j,k⟩
  · rw [markedMemoryPopulationStateCast_active]
    change (⟨j,d.activeId ((2*v+1)/2) j k⟩ : Σ j, A j) = ⟨j,d.activeId v j k⟩
    have he : (2*v+1)/2 = v := by omega
    rw [he]
  · rw [markedMemoryPopulationStateCast_pending]
    change (⟨j,(markedMemoryIndependentQueue hZ d (2*v+1) j).get (Fin.cast (by rfl) k)⟩ : Σ j, A j) =
      ⟨j,(markedMemoryIndependentQueue hZ d (2*v+1) j).get k⟩
    exact congrArg (fun k => (⟨j,(markedMemoryIndependentQueue hZ d (2*v+1) j).get k⟩ : Σ j, A j)) (Fin.ext rfl)

theorem markedMemoryIndependentGhostHits (v : ℕ) (hv : v ≤ n) :
    ∀ j i, (d.lifespan j).last ((markedMemoryIndependentQueue hZ d (2*v) j).get i) = 2*v →
      MarkedRawParticleHits (P j) (d.position v).1 (hZ _ (d.position v).2)
        (d.particle j ((markedMemoryIndependentQueue hZ d (2*v) j).get i)) := by
  intro j i hi
  have hm := (markedMemoryPendingQueueAt_mem (d.lifespan j) (2*v) (by omega) _).mp (List.get_mem _ i)
  exact d.ghost_death_hit v hv j _ hm.1 hi hm.2.2

theorem markedMemoryIndependentGhostAfter_bound (v : ℕ) (hv : v ≤ n) :
    (∑ j, (markedMemoryGhostQueueAfter (markedMemoryIndependentQueue hZ d (2*v))
      (fun j => (d.lifespan j).births (2*v)) (fun j => (d.lifespan j).last) (2*v) j).length) ≤ B := by
  rw [markedMemoryIndependentQueue_ghost hZ d v hv]
  exact markedMemoryIndependentQueue_bound hZ d (2*v+1) (by omega)

theorem markedMemoryIndependentGhost_label_step (v : ℕ) (hv : v ≤ n)
    (i : MarkedMemoryPopulationIndex (markedMemoryGhostChoiceTarget hZ
      (markedMemoryIndependentState hZ d v hv) (markedMemoryIndependentGhost hZ d v hv))) :
    Sum.elim (markedMemoryIndependentVertexValue hZ d v hv)
      (markedMemoryIndependentGhostBirthLabel hZ d v hv)
      (markedMemoryGhostPopulationOrigin hZ (markedMemoryIndependentState hZ d v hv)
        (markedMemoryIndependentGhost hZ d v hv) i) =
      markedMemoryIndependentPostGhostValue hZ d v hv
        (markedMemoryPopulationStateCast (markedMemoryIndependentGhost_target hZ d v hv) i) := by
  have hs := markedMemoryGhostQueueLabel_step hZ (d.position v)
    (fun j k => (d.particle j (d.activeId v j k)).1) (fun j k => d.activeId v j k)
    (markedMemoryIndependentQueue hZ d (2*v)) (fun j => (d.lifespan j).births (2*v))
    d.particle (fun j => (d.lifespan j).last) (2*v)
    (markedMemoryIndependentQueue_bound hZ d (2*v) (by omega))
    (markedMemoryIndependentGhostHits hZ d v hv) (markedMemoryIndependentGhostAfter_bound hZ d v hv) i
  have ht := markedMemoryGhostQueueTargetLabel_cast hZ (d.position v)
    (fun j k => (d.particle j (d.activeId v j k)).1) (fun j k => d.activeId v j k)
    (markedMemoryIndependentQueue hZ d (2*v)) (fun j => (d.lifespan j).births (2*v))
    d.particle (fun j => (d.lifespan j).last) (2*v)
    (markedMemoryIndependentQueue_bound hZ d (2*v) (by omega))
    (markedMemoryIndependentGhostHits hZ d v hv) (markedMemoryIndependentGhostAfter_bound hZ d v hv)
    (markedMemoryIndependentQueue hZ d (2*v+1)) (markedMemoryIndependentQueue_bound hZ d (2*v+1) (by omega))
    (markedMemoryIndependentQueue_ghost hZ d v hv) (markedMemoryIndependentGhost_target hZ d v hv) i
  exact hs.trans ht.symm

end
end ArtinMatthews
