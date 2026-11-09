module

public import ArtinMatthews.MarkedMemoryIndependentActivePath
public import ArtinMatthews.MarkedMemoryPathEndpointFamily


set_option backward.privateInPublic true
@[expose] public section

/-! The recovered active path uses exactly the original independent
initial state. Its initial nu atoms remain in the literal boundary
source measure, with chronological initial birth mass still one. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (hinj : Function.Injective (markedMemoryIndependentPrime hZ d))
  (hempty : ∀ j,(d.lifespan j).initial=[])

local notation "path" => markedMemoryIndependentActivePath hZ d hinj

include hempty

theorem markedMemoryIndependentActivePath_source :
    markedMemoryActivePathSource (B := B) path=markedMemoryIndependentState hZ d 0 (Nat.zero_le n) := by
  symm
  unfold markedMemoryIndependentState
  rw [markedMemory_initial_memory_empty hZ d hempty]
  rfl

theorem markedMemoryIndependentActivePath_initial_mass (ν : (j : J) → ↥(P j) → ℝ) :
    markedRawStateMass ν (markedMemoryActivePathSource (B := B) path)=
      markedMemoryInitialIdentityMass hZ d ν := by
  rw [markedMemoryIndependentActivePath_source hZ d hinj hempty]
  exact markedMemoryInitialIdentityMass_source hZ d hempty ν

theorem markedMemoryIndependentActivePath_source_mass (ν : (j : J) → ↥(P j) → ℝ) :
    markedRawStateMass ν (markedMemoryActivePathSource (B := B) path)=
      markedRawActiveMass ν (fun j k => (d.particle j (d.activeId 0 j k)).1) := by
  rw [markedMemoryIndependentActivePath_initial_mass hZ d hinj hempty]
  exact markedMemoryInitialIdentityMass_eq hZ d hempty ν

end
end ArtinMatthews
