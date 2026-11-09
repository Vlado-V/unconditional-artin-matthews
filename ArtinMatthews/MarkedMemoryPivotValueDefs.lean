module

public import ArtinMatthews.MarkedMemoryStageBirthMass
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeFixedCode


set_option backward.privateInPublic true
@[expose] public section

/-! The actual memo updates for initial slots, ghost batches and fresh
edge labels. This definitions-only layer is independent of row bounds. -/

noncomputable section
namespace ArtinMatthews

def markedMemoryInitialPivotValues
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes} {M B N : ℕ}
    (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes) (active : MarkedRawActive P M) :
    MarkedMemoryPotentialAddress J M B N → Option Nat.Primes :=
  markedMemoryStageBirthValues 0 old markedMemoryInitialDraw markedMemoryInitialDraw_injective
    (fun a => active a.1 a.2)

def markedMemoryGhostPivotValues
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes} {M B N : ℕ}
    (t : Fin (N+1)) (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes)
    (l : J → Fin (B+1)) (births : (j : J) → Fin (l j:ℕ) → ↥(P j)) :
    MarkedMemoryPotentialAddress J M B N → Option Nat.Primes :=
  markedMemoryStageBirthValues (2*t.1+1) old (markedMemoryGhostStageDraw t l)
    (markedMemoryGhostStageDraw_injective t l) (fun a => births a.1 a.2)

def markedMemoryEdgePivotValues
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes} {M B N pads : ℕ}
    (t : Fin N) (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes)
    {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (s : MarkedRawState P (pads+1) B Z) (c : MarkedRawEdgeChoice hZ s) :
    MarkedMemoryPotentialAddress J M B N → Option Nat.Primes :=
  markedMemoryStageBirthValues (2*t.1+2) old
    (markedMemoryEdgeStageDraw t (markedDirtyEdgePromotedGroups c.promotions))
    (markedMemoryEdgeStageDraw_injective t (markedDirtyEdgePromotedGroups c.promotions))
    (markedDirtyFixedEdgeChoiceCode hZ s (markedDirtyEdgePromotedGroups c.promotions) ⟨c,rfl⟩).2.2.2

end ArtinMatthews
