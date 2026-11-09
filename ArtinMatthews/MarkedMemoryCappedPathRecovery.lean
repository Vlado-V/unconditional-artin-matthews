module

public import ArtinMatthews.MarkedMemoryCappedPathSupport
public import ArtinMatthews.MarkedMemoryActivePathFinite
public import ArtinMatthews.MarkedMemoryIndependentUsedPrimeEquiv
public import ArtinMatthews.MarkedMemoryPathChoiceRecovery


set_option backward.privateInPublic true
@[expose] public section

/-! The actual active path and all optional primewise ghost endpoints
are recovered from the constructed, capped independent tableau. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads n B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (d : MarkedMemoryActivePathData P pads Z n)
  (c : MarkedMemoryPathPrimeChoices (P := P) (n := n))
  (hc : MarkedMemoryPathChoicesCompatible d hZ c)
  (hcap : MarkedMemoryPathCapacity hZ d c hc B)
  (births : MarkedMemoryEndpointBirthOrders (markedMemoryPathEndpointData hZ d c hc))
  (hP : ∀ i j,i≠j → Disjoint (P i) (P j))


theorem markedMemoryCappedPathIndependent_path :
    markedMemoryIndependentActivePath hZ (markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births) (markedMemoryCappedPathIndependent_prime_injective (B := B) hZ d c hc hcap births hP)=d := by
  apply markedMemoryActivePath_ext
  · funext v
    exact markedMemoryCappedPathIndependent_position hZ d c hc hcap births v
  · funext v j
    apply Function.Embedding.ext
    intro k
    change (((markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births)).particle j (((markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births)).activeId v.val j k)).1=d.active v j k
    rw [markedMemoryCappedPathIndependent_activeId,markedMemoryCappedPathIndependent_particle]
    rfl
  · funext v j
    change (((markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births)).particle j ((((markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births)).lifespan j).incoming (2*v.val+1))).1=d.incoming v j
    rw [markedMemoryCappedPathIndependent_incoming,markedMemoryCappedPathIndependent_particle]
    rfl
  · funext v j
    change (((markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births)).particle j ((((markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births)).lifespan j).outgoing (2*v.val+1))).1=d.outgoing v j
    rw [markedMemoryCappedPathIndependent_outgoing,markedMemoryCappedPathIndependent_particle]
    rfl

include hP in
theorem markedMemoryCappedPathIndependent_choices :
    markedMemoryIndependentPathChoices hZ (markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births)=c := by
  funext j p
  by_cases hu : MarkedMemoryPrimeLifespanUsed (markedMemoryPathVisits d j p) (c j p)
  · let a : MarkedMemoryPathUsedPrime d c j := ⟨p,hu⟩
    have hp : (((markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births)).particle j a).1=p := by
      rw [markedMemoryCappedPathIndependent_particle]
      rfl
    rw [← hp,markedMemoryIndependentPathChoices_at hZ (markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births) (markedMemoryCappedPathIndependent_prime_injective (B := B) hZ d c hc hcap births hP) j a]
    change markedMemoryPrimeChoiceOfInterval
      ((markedMemoryPathEndpointData hZ d c hc).first j a)
      ((markedMemoryPathEndpointData hZ d c hc).last j a)=c j p
    exact markedMemoryPrimeChoice_recover (markedMemoryPathPrimeLines hZ d p)
      (markedMemoryPathVisits d j p) (c j p) (hc j p) hu
  · have hp : ¬∃ a : MarkedMemoryPathUsedPrime d c j,(((markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births)).particle j a).1=p := by
      rintro ⟨a,ha⟩
      have he : a.1=p := by
        simpa only [markedMemoryCappedPathIndependent_particle,markedMemoryPathEndpointData,
          markedRawAnchoredParticle] using ha
      exact hu (he ▸ a.2)
    simp only [markedMemoryIndependentPathChoices,dite_eq_right hp]
    exact (not_not.mp (fun hn => hu (Or.inr hn))).symm

end
end ArtinMatthews
