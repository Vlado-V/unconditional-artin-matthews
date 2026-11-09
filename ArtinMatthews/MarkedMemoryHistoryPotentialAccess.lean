module

public import ArtinMatthews.MarkedMemoryPotentialBirths
public import ArtinMatthews.MarkedMemoryHistoryEdgeAccess


set_option backward.privateInPublic true
@[expose] public section

/-! The potential-address labels at each literal history vertex agree
with its actual ghost and slotted-edge choices. No prime injectivity or
independent reconstruction is required for these accessor identities. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)

theorem markedMemoryPotentialGhostValue_vertex
    {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (v : Fin (n+1)) (j : J) (k : Fin B) :
    markedMemoryPotentialGhostValue hZ history v j k=
      markedMemoryGhostPotentialValue (markedMemoryHistoryVertexGhost hZ history v) j k := by
  induction n generalizing s with
  | zero => have hv : v=0 := Fin.eq_zero v; subst v; rfl
  | succ n ih =>
    refine Fin.cases ?_ (fun w => ?_) v
    · rfl
    · exact ih history.2.2 w

theorem markedMemoryPotentialEdgeValue_vertex
    {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (v : Fin n) (j : J) :
    markedMemoryPotentialEdgeValue hZ history v j=
      markedMemoryEdgePotentialValue (markedMemoryHistoryVertexEdge hZ history v) j := by
  induction n generalizing s with
  | zero => exact Fin.elim0 v
  | succ n ih =>
    refine Fin.cases ?_ (fun w => ?_) v
    · rfl
    · exact ih history.2.2 w

theorem markedMemoryPotentialGhostValue_vertex_birth
    {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (v : Fin (n+1)) (j : J)
    (k : Fin ((markedMemoryHistoryVertexGhost hZ history v).sizes.1 j:ℕ)) :
    markedMemoryPotentialGhostValue hZ history v j
      ⟨k.1,k.2.trans_le (Nat.le_of_lt_succ ((markedMemoryHistoryVertexGhost hZ history v).sizes.1 j).2)⟩=
      some (((markedMemoryHistoryVertexGhost hZ history v).births j k).1) := by
  rw [markedMemoryPotentialGhostValue_vertex]
  exact markedMemoryGhostPotentialValue_birth _ j k

theorem markedMemoryPotentialGhostValue_vertex_absent
    {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (v : Fin (n+1)) (j : J) (k : Fin B)
    (hk : ¬k.1 < ((markedMemoryHistoryVertexGhost hZ history v).sizes.1 j:ℕ)) :
    markedMemoryPotentialGhostValue hZ history v j k=none := by
  rw [markedMemoryPotentialGhostValue_vertex,markedMemoryGhostPotentialValue,dite_eq_right hk]

end
end ArtinMatthews
