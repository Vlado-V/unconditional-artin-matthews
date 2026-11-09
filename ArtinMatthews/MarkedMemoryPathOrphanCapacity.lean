module

public import ArtinMatthews.MarkedMemoryPathEndpointCapacity
public import ArtinMatthews.MarkedMemoryPathPrimeCount


set_option backward.privateInPublic true
@[expose] public section

/-! The actual pending cutoff follows from the proved active/orphan
count. The supplied source capacity is retained without enlargement. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads n B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (d : MarkedMemoryActivePathData P pads Z n)
  (c : MarkedMemoryPathPrimeChoices (P := P) (n := n))
  (hc : MarkedMemoryPathChoicesCompatible d hZ c)

theorem markedMemoryPathEndpoint_pending_le_active_add_orphans (t : ℕ) :
    (∑ j,((markedMemoryEndpointCanonicalData (markedMemoryPathEndpointData hZ d c hc)).pendingAt t j).card)≤
      Fintype.card J*((n+1)*(pads+1))+markedMemoryPathOrphanCount d c :=
  (markedMemoryPathEndpoint_pending_le_used hZ d c hc t).trans (markedMemoryPathUsedPrime_total_card_le d c)

theorem markedMemoryPathCapacity_of_orphan_count
    (hcap : Fintype.card J*((n+1)*(pads+1))+markedMemoryPathOrphanCount d c≤B) :
    MarkedMemoryPathCapacity hZ d c hc B :=
  markedMemoryPathCapacity_of_used_card hZ d c hc ((markedMemoryPathUsedPrime_total_card_le d c).trans hcap)

def markedMemoryPathEndpointFamily_of_orphan_count
    (hcap : Fintype.card J*((n+1)*(pads+1))+markedMemoryPathOrphanCount d c≤B) :
    MarkedMemoryEndpointFamily (A := MarkedMemoryPathUsedPrime d c) (n := n) hZ
      (markedMemoryActivePathSource (B := B) d) :=
  markedMemoryPathEndpointFamily_of_cutoff hZ d c hc (markedMemoryPathCapacity_of_orphan_count hZ d c hc hcap)

end
end ArtinMatthews
