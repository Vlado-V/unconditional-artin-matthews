module

public import ArtinMatthews.MarkedMemoryPathEndpointData
public import ArtinMatthews.MarkedMemoryPrimeLifespanRecover


set_option backward.privateInPublic true
@[expose] public section

/-! Recovering optional ghost choices directly from the constructed
finite endpoint coordinates is an exact round trip. No chosen history
or inverse/correspondence premise is part of this decoding. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} {P : J → Finset Nat.Primes} {pads n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (d : MarkedMemoryActivePathData P pads Z n)
  (c : MarkedMemoryPathPrimeChoices (P := P) (n := n))
  (hc : MarkedMemoryPathChoicesCompatible d hZ c)

def markedMemoryPathEndpointDecodedChoices : MarkedMemoryPathPrimeChoices (P := P) (n := n) :=
  fun j p => if hu : MarkedMemoryPrimeLifespanUsed (markedMemoryPathVisits d j p) (c j p) then
    markedMemoryPrimeChoiceOfInterval
      ((markedMemoryPathEndpointData hZ d c hc).first j ⟨p,hu⟩)
      ((markedMemoryPathEndpointData hZ d c hc).last j ⟨p,hu⟩)
  else (none,none)

theorem markedMemoryPathEndpointDecodedChoices_eq :
    markedMemoryPathEndpointDecodedChoices hZ d c hc=c := by
  funext j p
  by_cases hu : MarkedMemoryPrimeLifespanUsed (markedMemoryPathVisits d j p) (c j p)
  · simp only [markedMemoryPathEndpointDecodedChoices,dite_eq_left hu]
    exact markedMemoryPrimeChoice_recover (markedMemoryPathPrimeLines hZ d p)
      (markedMemoryPathVisits d j p) (c j p) (hc j p) hu
  · simp only [markedMemoryPathEndpointDecodedChoices,dite_eq_right hu]
    exact (not_not.mp (fun hn => hu (Or.inr hn))).symm

end
end ArtinMatthews
