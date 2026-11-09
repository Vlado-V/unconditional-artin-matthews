module

public import ArtinMatthews.MarkedMemoryEdgeReconstruction


set_option backward.privateInPublic true
@[expose] public section

/-! Literal raw edge recovery retains target, store, old-only promotion
indices and the full target-last prime tuple. Fresh-label recovery is
proved through the actual degree-label equivalence. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

def markedMemoryRawEdgeTransport {s t : MarkedRawState P (pads+1) B Z} (h : s = t)
    (c : MarkedRawEdgeChoice hZ s) : MarkedRawEdgeChoice hZ t :=
  cast (congrArg (MarkedRawEdgeChoice hZ) h) c

theorem markedMemoryRawEdgeTransport_heq {s t : MarkedRawState P (pads+1) B Z} (h : s = t)
    (c : MarkedRawEdgeChoice hZ s) : HEq c (markedMemoryRawEdgeTransport hZ h c) := by
  cases h
  rfl

theorem markedMemoryRawEdgeTransport_target {s t : MarkedRawState P (pads+1) B Z} (h : s = t)
    (c : MarkedRawEdgeChoice hZ s) : (markedMemoryRawEdgeTransport hZ h c).target = c.target := by
  cases h
  rfl

theorem markedMemoryRawEdgeTransport_store {s t : MarkedRawState P (pads+1) B Z} (h : s = t)
    (c : MarkedRawEdgeChoice hZ s) : (markedMemoryRawEdgeTransport hZ h c).store = c.store := by
  cases h
  rfl

theorem markedMemoryRawEdgeTransport_promotions_some {s t : MarkedRawState P (pads+1) B Z} (h : s = t)
    (c : MarkedRawEdgeChoice hZ s) (j : J) (k : Fin (t.2.2.1.1 j : ℕ)) :
    (markedMemoryRawEdgeTransport hZ h c).promotions j = some k ↔
      c.promotions j = some (Fin.cast
        (congrArg (fun q : MarkedRawState P (pads+1) B Z => (q.2.2.1.1 j : ℕ)) h.symm) k) := by
  cases h
  rfl

theorem markedMemoryRawEdgeTransport_last {s t : MarkedRawState P (pads+1) B Z} (h : s = t)
    (c : MarkedRawEdgeChoice hZ s) :
    markedRawEdgeTargetLast t.2.2 (markedMemoryRawEdgeTransport hZ h c).promotions
      (markedMemoryRawEdgeTransport hZ h c).fresh = markedRawEdgeTargetLast s.2.2 c.promotions c.fresh := by
  cases h
  rfl

theorem markedMemoryRawEdgeChoice_eq_of_last {s : MarkedRawState P (pads+1) B Z}
    (a b : MarkedRawEdgeChoice hZ s) (ht : a.target = b.target) (hs : a.store = b.store)
    (hp : a.promotions = b.promotions)
    (hl : markedRawEdgeTargetLast s.2.2 a.promotions a.fresh =
      markedRawEdgeTargetLast s.2.2 b.promotions b.fresh) : a = b := by
  rcases a with ⟨ta,sa,pa,fa,hpa,hba⟩
  rcases b with ⟨tb,sb,pb,fb,hpb,hbb⟩
  dsimp only at ht hs hp hl
  cases ht
  cases hs
  cases hp
  have hf : fa = fb := by
    apply (markedRawEdgeDegreeLabelsEquiv s.2.2 pa).injective
    apply Subtype.ext
    simpa only [markedRawEdgeDegreeLabelsEquiv_value] using hl
  cases hf
  rfl

end
end ArtinMatthews
