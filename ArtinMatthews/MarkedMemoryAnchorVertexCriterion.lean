module

public import ArtinMatthews.MarkedMemoryHistoryAnchorGates
public import ArtinMatthews.MarkedMemoryTransitionDeterminismAccessors
public import ArtinMatthews.MarkedMemoryIndependentHistory


set_option backward.privateInPublic true
@[expose] public section

/-! A finite vertex criterion for the literal chronological anchor gate.
The criterion uses actual local edges and is compatible with the source
transports in the independent transition assembler. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)

theorem markedMemoryEdgeAnchorGate_heq
    {s t : MarkedRawState P (pads+1) B Z} (hs : s=t)
    (a : MarkedMemoryEdgeChoice hZ s) (b : MarkedMemoryEdgeChoice hZ t) (he : HEq a b) :
    MarkedMemoryEdgeAnchorGate hZ s a ↔ MarkedMemoryEdgeAnchorGate hZ t b := by
  cases hs
  cases eq_of_heq he
  rfl

theorem markedMemoryEdgeTransport_anchorGate
    {s t : MarkedRawState P (pads+1) B Z} (hs : s=t)
    (a : MarkedMemoryEdgeChoice hZ s) :
    MarkedMemoryEdgeAnchorGate hZ t (markedMemoryEdgeTransport hZ hs a) ↔
      MarkedMemoryEdgeAnchorGate hZ s a := by
  cases hs
  rfl

theorem markedMemoryHistoryAnchorAdmissible_iff_vertices
    {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ n s) :
    MarkedMemoryHistoryAnchorAdmissible hZ H ↔
      ∀ v : Fin n,MarkedMemoryEdgeAnchorGate hZ _ (markedMemoryHistoryVertexEdge hZ H v) := by
  induction n generalizing s with
  | zero => exact ⟨fun _ v => Fin.elim0 v,fun _ => trivial⟩
  | succ n ih =>
    constructor
    · rintro ⟨h0,ht⟩ v
      refine Fin.cases ?_ (fun w => ?_) v
      · exact h0
      · exact (ih H.2.2).mp ht w
    · intro hv
      exact ⟨hv 0,(ih H.2.2).mpr (fun w => hv w.succ)⟩

end
end ArtinMatthews
