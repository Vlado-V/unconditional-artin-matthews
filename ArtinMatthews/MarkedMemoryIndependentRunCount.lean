module

public import ArtinMatthews.MarkedMemoryHistoryPromotionVertices
public import ArtinMatthews.MarkedMemoryIndependentChoiceAccess


set_option backward.privateInPublic true
@[expose] public section

/-! Promotions are indexed directly by independent incoming identities
that occur in the old pending queue. The actual history/address map is
used only through its already proved equivalence and origin identities. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

omit [DecidableEq J] in
theorem markedMemoryHistoryPromotionVertex_origin {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (r : MarkedMemoryHistoryPromotionIndex hZ history) :
    let p := markedMemoryHistoryPromotionVertexEquiv hZ history r
    markedMemoryHistoryPromotionOrigin hZ history r =
      markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ history)
        (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history)
        ((2*p.1.val+1)+1) (Sum.inl ⟨p.2.1,
          ((markedMemoryHistoryVertexEdge hZ history p.1).2.2 p.2.1).symm (Fin.last pads)⟩) := by
  dsimp only
  refine (markedMemoryHistoryPromotion_target_origin hZ history r).symm.trans ?_
  rw [markedMemoryHistoryPromotionVertex_target]
  exact congrArg (fun t : ℕ => markedMemoryLineageOrigin
    (T := MarkedMemoryHistoryTracePopulation hZ history) (Birth := MarkedMemoryHistoryTraceBirth hZ history)
    (markedMemoryHistoryTraceStep hZ history) t
    (Sum.inl ⟨(markedMemoryHistoryPromotionVertexEquiv hZ history r).2.1,
      ((markedMemoryHistoryVertexEdge hZ history (markedMemoryHistoryPromotionVertexEquiv hZ history r).1).2.2
        (markedMemoryHistoryPromotionVertexEquiv hZ history r).2.1).symm (Fin.last pads)⟩))
    (congrArg (fun t => t+1) (markedMemoryHistoryPromotionVertex_time hZ history r))

variable {A : J → Type*} [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)] {n : ℕ}
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (order : Fin n → J → Equiv.Perm (Fin pads))

local notation "history" => markedMemoryIndependentHistory hZ d order

abbrev MarkedMemoryIndependentPromotions :=
  Σ v : Fin n, {j : J // (d.lifespan j).incoming (2*v.val+1) ∈
    markedMemoryIndependentQueue hZ d (2*v.val+1) j}

def markedMemoryIndependentPromotionEquiv :
    MarkedMemoryHistoryPromotionIndex hZ history ≃ MarkedMemoryIndependentPromotions hZ d :=
  (markedMemoryHistoryPromotionVertexEquiv hZ history).trans
    (Equiv.sigmaCongrRight (fun v => Equiv.subtypeEquivRight
      (fun j => markedMemoryIndependent_vertex_promoted_iff_mem hZ d order v j)))

def markedMemoryIndependentPromotionLabel (r : MarkedMemoryIndependentPromotions hZ d) : Σ j, A j :=
  ⟨r.2.1,(d.lifespan r.2.1).incoming (2*r.1.val+1)⟩

omit [DecidableEq J] in
theorem markedMemoryIndependentPromotion_origin_vertex (r : MarkedMemoryHistoryPromotionIndex hZ history) :
    let p := markedMemoryHistoryPromotionVertexEquiv hZ history r
    markedMemoryIndependentAddressEquiv hZ d order (markedMemoryHistoryPromotionOrigin hZ history r) =
      ⟨p.2.1,(d.lifespan p.2.1).incoming (2*p.1.val+1)⟩ := by
  dsimp only
  rw [markedMemoryHistoryPromotionVertex_origin]
  rw [markedMemoryIndependentAddress_active_slot hZ d order _ (by
    have h := (markedMemoryHistoryPromotionVertexEquiv hZ history r).1.isLt
    omega)]
  let p := markedMemoryHistoryPromotionVertexEquiv hZ history r
  change (⟨p.2.1,d.activeId (((2*p.1.val+1)+1)/2) p.2.1
    (((markedMemoryHistoryVertexEdge hZ history p.1).2.2 p.2.1).symm (Fin.last pads))⟩ : Σ j, A j) = _
  rw [show ((2*p.1.val+1)+1)/2 = p.1.val+1 by omega,
    markedMemoryIndependent_vertex_edge_targetSlots]
  have hi : (markedMemoryIndependentTargetSlots hZ d p.1.val p.1.2 (order p.1) p.2.1).symm
      (Fin.last pads) = markedMemoryIndependentIncoming hZ d p.1.val p.1.2 p.2.1 := by
    apply (markedMemoryIndependentTargetSlots hZ d p.1.val p.1.2 (order p.1) p.2.1).injective
    rw [Equiv.apply_symm_apply]
    exact (markedMemoryIndependentSlotPairs hZ d p.1.val p.1.2 (order p.1) p.2.1).2.2.1.symm
  rw [hi]
  exact congrArg (Sigma.mk p.2.1) (markedMemoryIndependentIncoming_eq hZ d p.1.val p.1.2 p.2.1)

omit [DecidableEq J] in
theorem markedMemoryIndependentPromotion_origin (r : MarkedMemoryHistoryPromotionIndex hZ history) :
    markedMemoryIndependentAddressEquiv hZ d order (markedMemoryHistoryPromotionOrigin hZ history r) =
      markedMemoryIndependentPromotionLabel hZ d (markedMemoryIndependentPromotionEquiv hZ d order r) :=
  markedMemoryIndependentPromotion_origin_vertex hZ d order r

def markedMemoryIndependentRunCount (a : Σ j, A j) : ℕ :=
  (Finset.univ.filter (fun v : Fin n => (d.lifespan a.1).incoming (2*v.val+1) = a.2 ∧
    a.2 ∈ markedMemoryIndependentQueue hZ d (2*v.val+1) a.1)).card

end
end ArtinMatthews
