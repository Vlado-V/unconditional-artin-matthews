module

public import ArtinMatthews.MarkedMemoryPathEndpointData
public import ArtinMatthews.MarkedMemoryEndpointLaws


set_option backward.privateInPublic true
@[expose] public section

/-! Bounded field formulas for the bare endpoint data constructed from
a compatible primewise choice. They keep the actual stage indices. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (d : MarkedMemoryActivePathData P pads Z n)
  (c : MarkedMemoryPathPrimeChoices (P := P) (n := n))
  (hc : MarkedMemoryPathChoicesCompatible d hZ c)

local notation "Used" => MarkedMemoryPathUsedPrime d c
local notation "E" => markedMemoryPathEndpointData hZ d c hc
local notation "C" => markedMemoryEndpointCanonicalData E

theorem markedMemoryPathEndpoint_active_even (v : Fin (n+1)) (j : J) (a : Used j) :
    (C).activeAt (2*v.val) j a ↔ ∃ k,d.active v j k=a.1 := by
  have ht : 2*v.val<2*n+2 := by have h:=v.isLt; omega
  change (if h : 2*v.val<2*n+2 then a∈(E).active ⟨2*v.val,h⟩ j else False) ↔ _
  rw [dite_eq_left ht,markedMemoryPathEndpoint_active]
  have he : (⟨(2*v.val)/2,by omega⟩ : Fin (n+1))=v := Fin.ext (by dsimp; omega)
  rw [he]

theorem markedMemoryPathEndpoint_active_odd (v : Fin (n+1)) (j : J) (a : Used j) :
    (C).activeAt (2*v.val+1) j a ↔ ∃ k,d.active v j k=a.1 := by
  have ht : 2*v.val+1<2*n+2 := by have h:=v.isLt; omega
  change (if h : 2*v.val+1<2*n+2 then a∈(E).active ⟨2*v.val+1,h⟩ j else False) ↔ _
  rw [dite_eq_left ht,markedMemoryPathEndpoint_active]
  have he : (⟨(2*v.val+1)/2,by omega⟩ : Fin (n+1))=v := Fin.ext (by dsimp; omega)
  rw [he]

theorem markedMemoryPathEndpoint_positionAt (v : Fin (n+1)) :
    (C).positionAt v.val=d.position v := (C).positionAt_valid v

theorem markedMemoryPathEndpoint_incomingAt (v : Fin n) (j : J) :
    (C).incomingAt (2*v.val+1) j=markedMemoryPathIncomingUsed d c v j := (C).incomingAt_valid v j

theorem markedMemoryPathEndpoint_outgoingAt (v : Fin n) (j : J) :
    (C).outgoingAt (2*v.val+1) j=markedMemoryPathOutgoingUsed d c v j := (C).outgoingAt_valid v j

theorem markedMemoryPathEndpoint_anchor (j : J) (a : Used j) :
    (C).particle j a=markedRawAnchoredParticle (P j) ((C).particle j a).1
      ((C).positionAt ((C).firstAt j a/2)).1 (hZ _ ((C).positionAt ((C).firstAt j a/2)).2) := by
  let v := markedMemoryPrimeBirthVisit (markedMemoryPathVisits d j a.1) (c j a.1)
  have he : v.val=(C).firstAt j a/2 := markedMemoryPrimeBirthVisit_eq_first_div _ _
  have hp : (C).positionAt ((C).firstAt j a/2)=d.position v := by
    rw [← he]
    exact markedMemoryPathEndpoint_positionAt hZ d c hc v
  rw [hp]
  rfl

end
end ArtinMatthews
