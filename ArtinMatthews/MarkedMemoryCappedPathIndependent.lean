module

public import ArtinMatthews.MarkedMemoryCappedPathConstruction
public import ArtinMatthews.MarkedMemoryFiniteProjection
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


attribute [local irreducible] markedMemoryCappedPathTableau

variable (births : MarkedMemoryEndpointBirthOrders (markedMemoryPathEndpointData hZ d c hc))

theorem markedMemoryCappedPathIndependent_initial (j : J) : (((markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births)).lifespan j).initial=[] := by
  let f := markedMemoryCappedPathTableau (B := B) hZ d c hc hcap births
  have he := markedMemoryFiniteProjection_initial hZ f j
  have hd := congrArg (fun u => markedMemoryFiniteList_toList (u.initial j))
    (markedMemoryCappedPathTableau_data (B := B) hZ d c hc hcap births)
  exact he.trans (hd.trans (markedMemoryFiniteList_toList_ofList [] List.nodup_nil))

theorem markedMemoryCappedPathIndependent_first (j : J) (a : MarkedMemoryPathUsedPrime d c j) :
    (((markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births)).lifespan j).first a=markedMemoryPrimeFirst (markedMemoryPathVisits d j a.1) (c j a.1) := by
  let f := markedMemoryCappedPathTableau (B := B) hZ d c hc hcap births
  have he := markedMemoryFiniteProjection_first hZ f j a
  have hd := congrArg (fun u => (u.first j a).val)
    (markedMemoryCappedPathTableau_data (B := B) hZ d c hc hcap births)
  exact he.trans hd

theorem markedMemoryCappedPathIndependent_last (j : J) (a : MarkedMemoryPathUsedPrime d c j) :
    (((markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births)).lifespan j).last a=markedMemoryPrimeLast (markedMemoryPathVisits d j a.1) (c j a.1) := by
  let f := markedMemoryCappedPathTableau (B := B) hZ d c hc hcap births
  have he := markedMemoryFiniteProjection_last hZ f j a
  have hd := congrArg (fun u => (u.last j a).val)
    (markedMemoryCappedPathTableau_data (B := B) hZ d c hc hcap births)
  exact he.trans hd

theorem markedMemoryCappedPathIndependent_position (v : Fin (n+1)) :
    ((markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births)).position v.val=d.position v := by
  let f := markedMemoryCappedPathTableau (B := B) hZ d c hc hcap births
  have he := markedMemoryFiniteProjection_position hZ f v
  have hd := congrArg (fun u => u.position v)
    (markedMemoryCappedPathTableau_data (B := B) hZ d c hc hcap births)
  exact he.trans hd

theorem markedMemoryCappedPathIndependent_activeId (v : Fin (n+1)) (j : J) (k : Fin (pads+1)) :
    ((markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births)).activeId v.val j k=markedMemoryPathActiveUsed d c v j k := by
  let f := markedMemoryCappedPathTableau (B := B) hZ d c hc hcap births
  have he := markedMemoryFiniteProjection_activeId hZ f v j k
  have hd := congrArg (fun u => u.activeId v j k)
    (markedMemoryCappedPathTableau_data (B := B) hZ d c hc hcap births)
  exact he.trans hd

theorem markedMemoryCappedPathIndependent_particle (j : J) (a : MarkedMemoryPathUsedPrime d c j) :
    ((markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births)).particle j a=((markedMemoryPathEndpointData hZ d c hc)).particle j a := by
  let f := markedMemoryCappedPathTableau (B := B) hZ d c hc hcap births
  have he := markedMemoryFiniteProjection_particle hZ f j a
  have hd := congrArg (fun u => u.particle j a)
    (markedMemoryCappedPathTableau_data (B := B) hZ d c hc hcap births)
  exact he.trans hd

theorem markedMemoryCappedPathIndependent_incoming (v : Fin n) (j : J) :
    (((markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births)).lifespan j).incoming (2*v.val+1)=markedMemoryPathIncomingUsed d c v j := by
  let f := markedMemoryCappedPathTableau (B := B) hZ d c hc hcap births
  have he := markedMemoryFiniteProjection_incoming hZ f v j
  have hd := congrArg (fun u => u.incoming v j)
    (markedMemoryCappedPathTableau_data (B := B) hZ d c hc hcap births)
  exact he.trans hd

theorem markedMemoryCappedPathIndependent_outgoing (v : Fin n) (j : J) :
    (((markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births)).lifespan j).outgoing (2*v.val+1)=markedMemoryPathOutgoingUsed d c v j := by
  let f := markedMemoryCappedPathTableau (B := B) hZ d c hc hcap births
  have he := markedMemoryFiniteProjection_outgoing hZ f v j
  have hd := congrArg (fun u => u.outgoing v j)
    (markedMemoryCappedPathTableau_data (B := B) hZ d c hc hcap births)
  exact he.trans hd

theorem markedMemoryCappedPathIndependent_normalized : MarkedMemoryBirthNormalized hZ (markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births) := by
  let f := markedMemoryCappedPathTableau (B := B) hZ d c hc hcap births
  have hn : markedMemoryFiniteAnchorNormalize hZ (markedMemoryEndpointDataDecorated (markedMemoryPathEndpointData hZ d c hc) births)=
      markedMemoryEndpointDataDecorated (markedMemoryPathEndpointData hZ d c hc) births :=
    (markedMemoryEndpointNormalize_iff hZ (markedMemoryPathEndpointData hZ d c hc) (markedMemoryEndpointCanonicalBirths (markedMemoryPathEndpointData hZ d c hc)) births).mp
      ((markedMemoryFiniteAnchorNormalize_fixed_iff hZ _).mpr (markedMemoryPathEndpoint_anchor hZ d c hc))
  have hd := congrArg (fun u => markedMemoryFiniteAnchorNormalize hZ u=u)
    (markedMemoryCappedPathTableau_data (B := B) hZ d c hc hcap births)
  exact (markedMemoryFiniteAnchorNormalize_admissible_fixed_iff hZ f).mp (Eq.mpr hd hn)

theorem markedMemoryCappedPathIndependent_terminal (j : J) :
    markedMemoryIndependentQueue hZ (markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births) (2*n+1) j=[] := by
  let f := markedMemoryCappedPathTableau (B := B) hZ d c hc hcap births
  apply List.eq_nil_of_length_eq_zero
  have he := markedMemoryFiniteProjection_queue_length hZ f (2*n+1) (Nat.le_refl _) j
  have hd := congrArg (fun u => (u.pendingAt (2*n+1) j).card)
    (markedMemoryCappedPathTableau_data (B := B) hZ d c hc hcap births)
  have hz : ((markedMemoryEndpointDataDecorated (markedMemoryPathEndpointData hZ d c hc) births).pendingAt (2*n+1) j).card=0 := by
    change ((markedMemoryEndpointCanonicalData (markedMemoryPathEndpointData hZ d c hc)).pendingAt (2*n+1) j).card=0
    rw [markedMemoryPathEndpoint_terminal_pending hZ d c hc j]
    rfl
  exact he.trans (hd.trans hz)

end
end ArtinMatthews
