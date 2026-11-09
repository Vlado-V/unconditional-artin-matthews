module

public import ArtinMatthews.MarkedMemoryEdgeOriginLabels
public import ArtinMatthews.MarkedMemoryLifespanEdgeQueue


set_option backward.privateInPublic true
@[expose] public section

/-! The target identity list of a queue-reconstructed edge is its
literal promotion-then-store queue. This small constructor calculation
avoids unfolding a whole independent schedule during later transport. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] {A : J → Type*}
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z target : Z)
  (active : MarkedRawActive P (pads+1)) (ids : (j : J) → Fin (pads+1) → A j)
  (queue : (j : J) → List (A j)) (hq : ∀ j, (queue j).Nodup)
  (incoming outgoing : (j : J) → A j) (store : J → Bool)
  (particle : (j : J) → A j → MarkedRawParticle (P j)) (hsource : (∑ j, (queue j).length) ≤ B)
  (hhit : ∀ j k, (queue j).get k = incoming j →
    MarkedRawParticleHits (P j) target.1 (hZ _ target.2) (particle j ((queue j).get k)))
  (htarget : (∑ j, (markedMemoryEdgeQueueAfter queue hq incoming outgoing store j).length) ≤ B)

theorem markedMemoryEdgeQueueLabel_pending_list
    (hout : ∀ j, ids j (Fin.last pads) = outgoing j) (j : J) :
    List.ofFn (fun k => markedMemoryEdgeTargetGroupLabel hZ
      (z,(active,markedMemoryLabeledQueueState queue particle hsource))
      (markedMemoryEdgeQueueChoice hZ z target active queue hq incoming outgoing store particle hsource hhit htarget)
      ids (fun j => (queue j).get) incoming j (Sum.inr k)) =
      markedMemoryEdgeQueueAfter queue hq incoming outgoing store j := by
  calc
    _ = _ := markedMemoryEdgeTargetGroupLabel_pending_list hZ
      (z,(active,markedMemoryLabeledQueueState queue particle hsource))
      (markedMemoryEdgeQueueChoice hZ z target active queue hq incoming outgoing store particle hsource hhit htarget)
      ids (fun j => (queue j).get) incoming j
    _ = _ := by
      change List.ofFn (fun k => (queue j).get
          ((Finset.univ \ (markedMemoryEdgeQueuePromotion queue hq incoming j).toFinset).orderEmbOfFin rfl k)) ++
          List.ofFn (fun _ : Fin (if store j then 1 else 0) => ids j (Fin.last pads)) = _
      rw [hout]
      unfold markedMemoryEdgeQueueAfter
      apply congrArg₂ (fun x y => x ++ y)
      · rfl
      · cases store j <;> simp

end
end ArtinMatthews
