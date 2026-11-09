module

public import ArtinMatthews.MarkedMemoryActivePathData
public import ArtinMatthews.MarkedMemoryEndpointData


set_option backward.privateInPublic true
@[expose] public section

/-! A compatible one-lifespan choice at each actual band prime gives
the bare finite endpoint data on exactly the used primes. No unused
particle labels or chronological history are stored. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryActivePathData P pads Z n)
  (c : MarkedMemoryPathPrimeChoices (P := P) (n := n))
  (hc : MarkedMemoryPathChoicesCompatible d hZ c)

def markedMemoryPathPrimeLines {j : J} (p : P j) : Fin (n+1) → MarkedRawPrimeLine p.1 :=
  fun v => markedPrimePositionLine (p.1:ℕ) (d.position v).1 (hZ _ (d.position v).2)

local notation "Used" => MarkedMemoryPathUsedPrime d c
local notation "visits" => markedMemoryPathVisits d
local notation "lines" => markedMemoryPathPrimeLines hZ d

def markedMemoryPathActiveUsed (v : Fin (n+1)) (j : J) : Fin (pads+1) ↪ Used j where
  toFun k := ⟨d.active v j k,Or.inl ⟨v,(markedMemoryPathVisits_mem d j _ v).mpr ⟨k,rfl⟩⟩⟩
  inj' := fun _ _ h => (d.active v j).injective (congrArg Subtype.val h)

def markedMemoryPathIncomingUsed (v : Fin n) (j : J) : Used j :=
  ⟨d.incoming v j,Or.inl ⟨v.succ,(markedMemoryPathVisits_mem d j _ v.succ).mpr (d.incoming_present v j)⟩⟩

def markedMemoryPathOutgoingUsed (v : Fin n) (j : J) : Used j :=
  ⟨d.outgoing v j,Or.inl ⟨v.castSucc,(markedMemoryPathVisits_mem d j _ v.castSucc).mpr (d.outgoing_present v j)⟩⟩

def markedMemoryPathEndpointData : MarkedMemoryEndpointData Used P pads Z n where
  first j a := ⟨markedMemoryPrimeFirst (visits j a.1) (c j a.1),by
    have h₁ := markedMemoryPrimeLifespan_nonempty (lines a.1) (visits j a.1) (c j a.1) (hc j a.1) a.2
    have h₂ := markedMemoryPrimeLast_bound (visits j a.1) (c j a.1)
    omega⟩
  last j a := ⟨markedMemoryPrimeLast (visits j a.1) (c j a.1),by
    have h := markedMemoryPrimeLast_bound (visits j a.1) (c j a.1)
    omega⟩
  active t j := Finset.univ.filter (fun a => (⟨t.val/2,by have h:=t.isLt; omega⟩ : Fin (n+1))∈visits j a.1)
  incoming := markedMemoryPathIncomingUsed d c
  outgoing := markedMemoryPathOutgoingUsed d c
  position := d.position
  activeId := markedMemoryPathActiveUsed d c
  particle j a := markedRawAnchoredParticle (P j) a.1
    (d.position (markedMemoryPrimeBirthVisit (visits j a.1) (c j a.1))).1
    (hZ _ (d.position (markedMemoryPrimeBirthVisit (visits j a.1) (c j a.1))).2)

omit [Fintype J] in
theorem markedMemoryPathEndpoint_first (j : J) (a : Used j) :
    ((markedMemoryPathEndpointData hZ d c hc).first j a).val=
      markedMemoryPrimeFirst (visits j a.1) (c j a.1) := rfl

omit [Fintype J] in
theorem markedMemoryPathEndpoint_last (j : J) (a : Used j) :
    ((markedMemoryPathEndpointData hZ d c hc).last j a).val=
      markedMemoryPrimeLast (visits j a.1) (c j a.1) := rfl

omit [Fintype J] in
theorem markedMemoryPathEndpoint_active (t : Fin (2*n+2)) (j : J) (a : Used j) :
    a∈(markedMemoryPathEndpointData hZ d c hc).active t j ↔
      ∃ k,d.active ⟨t.val/2,by have h:=t.isLt; omega⟩ j k=a.1 := by
  simp only [markedMemoryPathEndpointData,Finset.mem_filter,Finset.mem_univ,true_and,
    markedMemoryPathVisits_mem]

omit [Fintype J] in
theorem markedMemoryPathEndpoint_position (v : Fin (n+1)) :
    (markedMemoryPathEndpointData hZ d c hc).position v=d.position v := rfl

omit [Fintype J] in
theorem markedMemoryPathEndpoint_particle (j : J) (a : Used j) :
    (markedMemoryPathEndpointData hZ d c hc).particle j a=
      markedRawAnchoredParticle (P j) a.1
        (d.position (markedMemoryPrimeBirthVisit (visits j a.1) (c j a.1))).1
        (hZ _ (d.position (markedMemoryPrimeBirthVisit (visits j a.1) (c j a.1))).2) := rfl

end
end ArtinMatthews
