module

public import ArtinMatthews.MarkedMemoryGhostReconstruction
public import ArtinMatthews.MarkedMemoryLifespanSurvival


set_option backward.privateInPublic true
@[expose] public section

/-! Reverse a ghost step from literal lifespan endpoints and an ordered
list of the newly born prime labels. Old deaths are recovered as exactly
the endpoints equal to the current time. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {M B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P M B Z)

def markedMemoryLifespanRetained (t : ℕ) (last : (j : J) → Fin (s.2.2.1.1 j : ℕ) → ℕ)
    (j : J) : Finset (Fin (s.2.2.1.1 j : ℕ)) := Finset.univ.filter (fun k => t < last j k)

def markedMemoryGhostFromLifespans (t : ℕ)
    (last : (j : J) → Fin (s.2.2.1.1 j : ℕ) → ℕ) (born : (j : J) → List (↥(P j)))
    (hold : ∀ j k, t ≤ last j k)
    (hdeath : ∀ j k, last j k = t → k ∈ markedRawGroupHitIndices s.2.2 j s.1.1 (hZ _ s.1.2))
    (hbound : (∑ j, ((markedMemoryLifespanRetained s t last j).card + (born j).length)) ≤ B) :
    MarkedMemoryGhostRunData hZ s where
  retained := markedMemoryLifespanRetained s t last
  born := born
  deaths_hit := by
    intro j k hk
    have hk' : ¬ t < last j k := by simpa only [markedMemoryLifespanRetained,
      Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and] using hk
    exact hdeath j k (by have := hold j k; omega)
  memory_bound := hbound

/-- Every old deletion of the reconstructed choice is exactly an actual
lifespan ending now; continuing identities are never deleted. -/
theorem markedMemoryGhostFromLifespans_deleted (t : ℕ)
    (last : (j : J) → Fin (s.2.2.1.1 j : ℕ) → ℕ) (born : (j : J) → List (↥(P j)))
    (hold : ∀ j k, t ≤ last j k)
    (hdeath : ∀ j k, last j k = t → k ∈ markedRawGroupHitIndices s.2.2 j s.1.1 (hZ _ s.1.2))
    (hbound : (∑ j, ((markedMemoryLifespanRetained s t last j).card + (born j).length)) ≤ B)
    (j : J) (k : Fin (s.2.2.1.1 j : ℕ)) :
    k ∈ (markedMemoryGhostRunReconstruct hZ s
      (markedMemoryGhostFromLifespans hZ s t last born hold hdeath hbound)).deletion j ↔ last j k = t := by
  change k ∈ Finset.univ \ markedMemoryLifespanRetained s t last j ↔ _
  simp only [markedMemoryLifespanRetained, Finset.mem_sdiff, Finset.mem_univ,
    Finset.mem_filter, true_and]
  have := hold j k
  omega

variable {pads n : ℕ} {s₀ : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s₀)

def markedMemoryHistoryHeadGhostLast (j : J) (k : Fin (s₀.2.2.1.1 j : ℕ)) : ℕ :=
  markedMemoryHistoryLifespanLast hZ history (Sum.inl (Sum.inr ⟨j,k⟩))

theorem markedMemoryHistoryHeadGhostLast_retained (j : J) :
    markedMemoryLifespanRetained s₀ 0 (markedMemoryHistoryHeadGhostLast hZ history) j =
      markedRawGhostSurvivors s₀.2.2 (markedMemoryHistoryHeadGhost hZ history).deletion j := by
  apply Finset.ext
  intro k
  constructor
  · intro hk
    apply (markedMemoryHistory_head_ghost_retained_iff_last hZ history j k).mpr
    exact (Finset.mem_filter.mp hk).2
  · intro hk
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, (markedMemoryHistory_head_ghost_retained_iff_last hZ history j k).mp hk⟩

/-- The independently specified endpoint rule is admissible for the
computed lifespans of every actual history. -/
def markedMemoryHistoryHeadGhostLifespanData : MarkedMemoryGhostRunData hZ s₀ :=
  markedMemoryGhostFromLifespans hZ s₀ 0 (markedMemoryHistoryHeadGhostLast hZ history)
    (fun j => List.ofFn ((markedMemoryHistoryHeadGhost hZ history).births j))
    (fun _ _ => Nat.zero_le _)
    (fun j k hk => (markedMemoryHistoryHeadGhost hZ history).allowed j
      ((markedMemoryHistory_head_ghost_deleted_iff_last hZ history j k).mpr hk))
    (by simpa only [markedMemoryHistoryHeadGhostLast_retained, List.length_ofFn] using
      (markedMemoryHistoryHeadGhost hZ history).sizes.2)

theorem markedMemoryHistoryHeadGhostLifespanData_eq :
    markedMemoryHistoryHeadGhostLifespanData hZ history =
      markedMemoryGhostRunEncode hZ s₀ (markedMemoryHistoryHeadGhost hZ history) := by
  apply MarkedMemoryGhostRunData.ext
  · funext j
    exact markedMemoryHistoryHeadGhostLast_retained hZ history j
  · rfl

/-- Forward computed endpoints followed by the literal reverse rule
recover the original ghost choice, including all ordered birth labels. -/
theorem markedMemoryHistory_head_ghost_reconstructed :
    markedMemoryGhostRunReconstruct hZ s₀ (markedMemoryHistoryHeadGhostLifespanData hZ history) =
      markedMemoryHistoryHeadGhost hZ history := by
  rw [markedMemoryHistoryHeadGhostLifespanData_eq, markedMemoryGhostRun_reconstruct_encode]

end
end ArtinMatthews
