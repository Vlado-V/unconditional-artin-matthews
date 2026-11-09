module

public import ArtinMatthews.MarkedMemoryHistoryEdgeOrigins


set_option backward.privateInPublic true
@[expose] public section

/-! Prime-label preservation for the genuine global edge-population origin injection. -/
namespace ArtinMatthews
noncomputable section

/-- The prime of an actually performed fresh edge birth. Promoted groups have no such address. -/
def markedMemoryEdgeFreshOriginPrime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) : {j : J // choice.promotions j = none} → Nat.Primes :=
  fun j => (markedRawEdgeTargetLast s.2.2 choice.promotions choice.fresh j.1).1

/-- Plain indexed formula for an active target slot's global origin. -/
theorem markedMemoryEdgePopulationOrigin_active {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) (j : J) (i : Fin (pads+1)) :
    markedMemoryEdgePopulationOrigin hZ s choice (Sum.inl ⟨j, i⟩) =
      Sum.map (Sum.map (Sigma.mk j) (Sigma.mk j))
        (fun h : PLift (choice.promotions j = none) => ⟨j, h.down⟩)
        (markedMemoryEdgeGroupOrigin hZ s choice j (Sum.inl i)) := by
  change (Equiv.sumCongr (markedMemoryPopulationGroupEquiv s).symm
    (Equiv.sigmaPLiftEquivSubtype (fun j => choice.promotions j = none)))
      ((Equiv.sigmaSumDistrib
        (fun j => Fin (pads+1) ⊕ Fin (s.2.2.1.1 j : ℕ))
        (fun j => PLift (choice.promotions j = none)))
        ⟨j, markedMemoryEdgeGroupOrigin hZ s choice j (Sum.inl i)⟩) = _
  generalize hout : markedMemoryEdgeGroupOrigin hZ s choice j (Sum.inl i) = o
  rcases o with (old | old) | fresh <;> rfl

/-- Plain indexed formula for a pending target slot's global origin. -/
theorem markedMemoryEdgePopulationOrigin_pending {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) (j : J)
    (i : Fin ((markedRawEdgeTargetMemory hZ s choice).1.1 j : ℕ)) :
    markedMemoryEdgePopulationOrigin hZ s choice (Sum.inr ⟨j, i⟩) =
      Sum.map (Sum.map (Sigma.mk j) (Sigma.mk j))
        (fun h : PLift (choice.promotions j = none) => ⟨j, h.down⟩)
        (markedMemoryEdgeGroupOrigin hZ s choice j (Sum.inr i)) := by
  change (Equiv.sumCongr (markedMemoryPopulationGroupEquiv s).symm
    (Equiv.sigmaPLiftEquivSubtype (fun j => choice.promotions j = none)))
      ((Equiv.sigmaSumDistrib
        (fun j => Fin (pads+1) ⊕ Fin (s.2.2.1.1 j : ℕ))
        (fun j => PLift (choice.promotions j = none)))
        ⟨j, markedMemoryEdgeGroupOrigin hZ s choice j (Sum.inr i)⟩) = _
  generalize hout : markedMemoryEdgeGroupOrigin hZ s choice j (Sum.inr i) = o
  rcases o with (old | old) | fresh <;> rfl

/-- The actual global indexed route preserves every target prime, including repeated values. -/
theorem markedMemoryEdgePopulationOrigin_prime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s)
    (i : MarkedMemoryPopulationIndex (markedRawEdgeTargetState hZ s choice)) :
    Sum.elim (markedMemoryPopulationPrime s) (markedMemoryEdgeFreshOriginPrime hZ s choice)
      (markedMemoryEdgePopulationOrigin hZ s choice i) =
        markedMemoryPopulationPrime (markedRawEdgeTargetState hZ s choice) i := by
  rcases i with ⟨j, i⟩ | ⟨j, i⟩
  · rw [markedMemoryEdgePopulationOrigin_active]
    have h := markedMemoryEdgeGroupOrigin_prime hZ s choice j (Sum.inl i)
    change Sum.elim (markedMemoryPopulationGroupPrime s j)
      (fun _ : PLift (choice.promotions j = none) =>
        (markedRawEdgeTargetLast s.2.2 choice.promotions choice.fresh j).1)
      (markedMemoryEdgeGroupOrigin hZ s choice j (Sum.inl i)) = ((markedRawEdgeTargetState hZ s choice).2.1 j i).1 at h
    generalize hout : markedMemoryEdgeGroupOrigin hZ s choice j (Sum.inl i) = o at h ⊢
    rcases o with (old | old) | fresh
    all_goals
      simpa only [Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr,
        markedMemoryPopulationPrime, markedMemoryPopulationGroupPrime,
        markedMemoryEdgeFreshOriginPrime] using h
  · erw [markedMemoryEdgePopulationOrigin_pending hZ s choice j i]
    have h := markedMemoryEdgeGroupOrigin_prime hZ s choice j (Sum.inr i)
    change Sum.elim (markedMemoryPopulationGroupPrime s j)
      (fun _ : PLift (choice.promotions j = none) =>
        (markedRawEdgeTargetLast s.2.2 choice.promotions choice.fresh j).1)
      (markedMemoryEdgeGroupOrigin hZ s choice j (Sum.inr i)) = ((markedRawEdgeTargetState hZ s choice).2.2.2 j i).1.1 at h
    generalize hout : markedMemoryEdgeGroupOrigin hZ s choice j (Sum.inr i) = o at h ⊢
    rcases o with (old | old) | fresh
    all_goals
      simpa only [Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr,
        markedMemoryPopulationPrime, markedMemoryPopulationGroupPrime,
        markedMemoryEdgeFreshOriginPrime] using h

end
end ArtinMatthews
