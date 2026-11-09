module

public import ArtinMatthews.MarkedMemoryActualQueueData
public import ArtinMatthews.MarkedMemoryActualPhysicalLabels
public import ArtinMatthews.MarkedMemoryIndependentLifespans


set_option backward.privateInPublic true
@[expose] public section

/-! An independent admissible tableau extracted from an actual history.
Its fields are computed endpoints, identity slots, ordered birth batches,
positions and static particles; it contains no chronological history field. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)

theorem markedMemoryActualPendingIdentitySet_card (t : ℕ) (ht : t ≤ 2*n+1) (j : J) :
    (markedMemoryPendingIdentitySet (markedMemoryActualQueueData hZ history j) t).card =
      ((markedMemoryHistoryTraceState hZ history t).2.2.1.1 j : ℕ) := by
  have he : markedMemoryPendingIdentitySet (markedMemoryActualQueueData hZ history j) t =
      (markedMemoryActualPendingQueue hZ history t j).toFinset := by
    ext a
    simp only [markedMemoryPendingIdentitySet,Finset.mem_filter,Finset.mem_univ,true_and,List.mem_toFinset]
    exact (markedMemoryActualPendingQueue_interval hZ history t ht j a).symm
  rw [he,List.toFinset_card_of_nodup (markedMemoryActualPendingQueue_nodup hZ history t j)]
  exact markedMemoryActualPendingQueue_length hZ history t j

theorem markedMemoryActualPendingIdentitySet_bound (t : ℕ) (ht : t ≤ 2*n+1) :
    (∑ j, (markedMemoryPendingIdentitySet (markedMemoryActualQueueData hZ history j) t).card) ≤ B := by
  simp_rw [markedMemoryActualPendingIdentitySet_card hZ history t ht]
  exact (markedMemoryHistoryTraceState hZ history t).2.2.1.2

def markedMemoryActualTableau (ha : MarkedMemoryHistoryAnchorAdmissible hZ history) :
    MarkedMemoryIndependentLifespans (A := MarkedMemoryActualFiber hZ history)
      (P := P) (pads := pads) (B := B) hZ n where
  lifespan := markedMemoryActualQueueData hZ history
  position := markedMemoryActualPosition hZ history
  activeId := fun v => markedMemoryActualActiveIds hZ history (2*v)
  particle := markedMemoryActualParticle hZ history
  active_mem := fun _ _ _ _ => Iff.rfl
  active_alive := markedMemoryActualActiveIds_alive hZ history
  cutoff := markedMemoryActualPendingIdentitySet_bound hZ history
  ghost_death_hit := markedMemoryActual_ghost_death_hit hZ history ha
  ghost_birth_anchor := markedMemoryActual_ghost_birth_anchor hZ history ha
  promotion_hit := by
    intro v hv j _hf _hl _hn
    change MarkedRawParticleHits (P j) (markedMemoryActualPosition hZ history (v+1)).1
      (hZ _ (markedMemoryActualPosition hZ history (v+1)).2)
      (markedMemoryActualParticle hZ history j (markedMemoryActualIncomingAt hZ history (2*v+1) j))
    rw [markedMemoryActualIncomingAt_edge hZ history ⟨v,hv⟩ j]
    exact markedMemoryActual_incoming_hit hZ history ha ⟨v,hv⟩ j
  store_anchor := by
    intro v hv j _hl
    change markedMemoryActualParticle hZ history j (markedMemoryActualOutgoingAt hZ history (2*v+1) j) =
      markedRawAnchoredParticle (P j)
        (markedMemoryActualParticle hZ history j (markedMemoryActualOutgoingAt hZ history (2*v+1) j)).1
        (markedMemoryActualPosition hZ history v).1 (hZ _ (markedMemoryActualPosition hZ history v).2)
    rw [markedMemoryActualOutgoingAt_edge hZ history ⟨v,hv⟩ j]
    exact markedMemoryActual_outgoing_anchor hZ history ha ⟨v,hv⟩ j

/-- The physical admissibility needed above is a theorem of a nonzero
literal chronological coefficient, not a premise about lifespan weights. -/
def markedMemoryActualTableau_of_weight_ne_zero
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (j : ℕ)
    (hw : markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history ≠ 0) :
    MarkedMemoryIndependentLifespans (A := MarkedMemoryActualFiber hZ history)
      (P := P) (pads := pads) (B := B) hZ n :=
  markedMemoryActualTableau hZ history
    (markedMemoryHistoryAnchorAdmissible_of_weight_ne_zero ν V hZ ψ η d₀ Y Q ρ qStage χ n j history hw)

end
end ArtinMatthews
