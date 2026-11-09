module

public import ArtinMatthews.MarkedMemoryFiniteTableau
public import ArtinMatthews.MarkedMemoryActualFibers


set_option backward.privateInPublic true
@[expose] public section

/-! Finiteness is proved for both explicit bounded identity families and
the genuine finite trace-address fibers. No finiteness assumption on an
unbounded lifespan record type is used. -/
namespace ArtinMatthews
noncomputable section

theorem markedMemoryFiniteTableau_finIDs_finite
    {J : Type*} [Fintype J] (N : J → ℕ) {P : J → Finset Nat.Primes}
    {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) :
    Finite (MarkedMemoryFiniteTableau (A := fun j => Fin (N j))
      (P := P) (pads := pads) (B := B) hZ n) := inferInstance

theorem markedMemoryActualFiniteTableau_finite
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    {s : MarkedRawState P (pads+1) B Z} (history : MarkedMemoryChronologicalHistory hZ n s) :
    Finite (MarkedMemoryFiniteTableau (A := MarkedMemoryActualFiber hZ history)
      (P := P) (pads := pads) (B := B) hZ n) := inferInstance

end
end ArtinMatthews
