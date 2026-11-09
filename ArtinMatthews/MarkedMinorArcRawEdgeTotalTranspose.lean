module

public import ArtinMatthews.MarkedMinorArcRawEdgeCoupledTranspose
public import ArtinMatthews.MarkedMinorArcRawEdgeDegreeChoices
public import ArtinMatthews.MarkedMinorArcRawMemoryDegreeFamily


set_option backward.privateInPublic true
@[expose] public section

/-! Finite total-memory cutoffs in the coupled edge transpose.  The two
literal cutoffs are exchanged by the actual promoted/stored flag swap. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

def markedRawEdgeDegreePairing
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset Nat.Primes) (ν : (j : J) → ↥(P j) → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (x y : Z)
    (copied : MarkedRawActive P pads) (t : MarkedRawEdgeDegrees J B) (δ γ : J → ℂ)
    (K : MarkedRawState P (pads+1) B Z → MarkedRawState P (pads+1) B Z → ℂ) : ℂ :=
  ∑ a : (j : J) → ↥(P j), (∏ j, ν j (a j)) *
    ∑ old : (j : J) → Fin (t.survivors j + markedRawEdgeBit (t.promoted j)) →
      MarkedRawParticle (P j),
      ((∏ j, ∏ i, ν j (old j i).1) /
        (∏ j, (Nat.factorial (t.survivors j + markedRawEdgeBit (t.promoted j)) : ℂ))) *
        markedRawEdgeSlotComponent P ν x.1 y.1 (hZ _ x.2) (hZ _ y.2) t.survivors
          (fun j => markedRawEdgeBit (t.promoted j))
          (fun j => markedRawEdgeBit (t.stored j)) δ γ a
          (fun old b new => K
            (x, ((markedRawActiveSplit pads).symm (copied,a),
              markedRawMemoryOfDegrees P
                (fun j => t.survivors j + markedRawEdgeBit (t.promoted j)) t.source_le old))
            (y, ((markedRawActiveSplit pads).symm (copied,b),
              markedRawMemoryOfDegrees P
                (fun j => t.survivors j + markedRawEdgeBit (t.stored j)) t.target_le new))) old

/-- A single actual source/target degree pair transposes to its flag swap.
Only independent pending-index symmetry of the joint kernel is required. -/
theorem markedRawEdge_degree_pairing_transpose
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset Nat.Primes) (ν : (j : J) → ↥(P j) → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (x y : Z)
    (copied : MarkedRawActive P pads) (t : MarkedRawEdgeDegrees J B) (δ γ : J → ℂ)
    (K : MarkedRawState P (pads+1) B Z → MarkedRawState P (pads+1) B Z → ℂ)
    (hKleft : ∀ z active target, MarkedRawMemorySymmetric (fun m => K (z,(active,m)) target))
    (hKright : ∀ source z active, MarkedRawMemorySymmetric (fun m => K source (z,(active,m)))) :
    markedRawEdgeDegreePairing P ν hZ x y copied t δ γ K =
      markedRawEdgeDegreePairing P ν hZ y x copied (markedRawEdgeDegreesSwap t) γ δ
        (fun target source => K source target) := by
  unfold markedRawEdgeDegreePairing
  apply markedRawEdge_slot_component_transpose
  · exact fun j => markedRawEdgeBit_le_one _
  · exact fun j => markedRawEdgeBit_le_one _
  · intro a b new
    exact markedRawMemory_symmetric_degree_family _
      (hKleft _ _ _) _ _
  · intro a old b
    exact markedRawMemory_symmetric_degree_family _
      (hKright _ _ _) _ _

/-- Exact coupled edge transpose across all allowed source and target
pending degrees.  The two original total-memory restrictions are retained
and exchanged; no independent per-group replacement cutoff is introduced. -/
theorem markedRawEdge_total_degree_transpose
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset Nat.Primes) (ν : (j : J) → ↥(P j) → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (x y : Z)
    (copied : MarkedRawActive P pads) (δ γ : J → ℂ)
    (K : MarkedRawState P (pads+1) B Z → MarkedRawState P (pads+1) B Z → ℂ)
    (hKleft : ∀ z active target, MarkedRawMemorySymmetric (fun m => K (z,(active,m)) target))
    (hKright : ∀ source z active, MarkedRawMemorySymmetric (fun m => K source (z,(active,m)))) :
    (∑ t : MarkedRawEdgeDegrees J B, markedRawEdgeDegreePairing P ν hZ x y copied t δ γ K) =
      ∑ t : MarkedRawEdgeDegrees J B, markedRawEdgeDegreePairing P ν hZ y x copied t γ δ
        (fun target source => K source target) := by
  calc
    _ = ∑ t : MarkedRawEdgeDegrees J B,
        markedRawEdgeDegreePairing P ν hZ y x copied (markedRawEdgeDegreesSwap t) γ δ
          (fun target source => K source target) := by
      apply Finset.sum_congr rfl
      intro t _
      exact markedRawEdge_degree_pairing_transpose P ν hZ x y copied t δ γ K hKleft hKright
    _ = _ := (markedRawEdgeDegreesSwap (J := J) (B := B)).sum_comp
      (fun t => markedRawEdgeDegreePairing P ν hZ y x copied t γ δ
        (fun target source => K source target))

end
end ArtinMatthews
