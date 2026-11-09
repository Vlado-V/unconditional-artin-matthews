module

public import ArtinMatthews.MarkedMemoryPathEndpointCapacity
public import ArtinMatthews.MarkedMemoryEndpointFactors
public import ArtinMatthews.MarkedMemoryPathEndpointTerminalSet


set_option backward.privateInPublic true
@[expose] public section

/-! The independent tableau of a compatible prime path at its actual
pending capacity. Birth orders are retained explicitly; all interval,
active and particle fields come from the computed bare family. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads n B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (d : MarkedMemoryActivePathData P pads Z n)
  (c : MarkedMemoryPathPrimeChoices (P := P) (n := n))
  (hc : MarkedMemoryPathChoicesCompatible d hZ c)
  (hcap : MarkedMemoryPathCapacity hZ d c hc B)

local notation "E" => markedMemoryPathEndpointData hZ d c hc

def markedMemoryCappedPathTableau (births : MarkedMemoryEndpointBirthOrders E) :
    @MarkedMemoryFiniteTableau J inferInstance (MarkedMemoryPathUsedPrime d c)
      (markedMemoryPathUsedPrime_fintype d c) P pads B Z hZ n :=
    ⟨markedMemoryEndpointDataDecorated E births,
      markedMemoryEndpointLaws_transfer hZ E (markedMemoryEndpointCanonicalBirths E) births
        (markedMemoryPathEndpoint_laws_of_cutoff hZ d c hc hcap)⟩

theorem markedMemoryCappedPathTableau_data (births : MarkedMemoryEndpointBirthOrders E) :
    (markedMemoryCappedPathTableau (B := B) hZ d c hc hcap births).1=
      markedMemoryEndpointDataDecorated E births := rfl

def markedMemoryCappedPathIndependent (births : MarkedMemoryEndpointBirthOrders E) :
    @MarkedMemoryIndependentLifespans J inferInstance (MarkedMemoryPathUsedPrime d c)
      (markedMemoryPathUsedPrime_fintype d c) P pads B Z hZ n :=
  markedMemoryFiniteTableau_toIndependent hZ (markedMemoryCappedPathTableau (B := B) hZ d c hc hcap births)

end
end ArtinMatthews
