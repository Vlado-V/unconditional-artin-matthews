module

public import ArtinMatthews.MarkedMemoryFiniteTableauData


set_option backward.privateInPublic true
@[expose] public section

/-! Restriction discards only the unused Nat-indexed tail of an existing
admissible lifespan record. Every meaningful coordinate is recovered. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)} {n : ℕ}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

def markedMemoryFiniteData_ofIndependent : MarkedMemoryFiniteTableauData A P pads Z n where
  first := fun j a => ⟨(d.lifespan j).first a,by
    have h := (d.lifespan j).nonempty a
    have hh := (d.lifespan j).bounded a
    omega⟩
  last := fun j a => ⟨(d.lifespan j).last a,by have h := (d.lifespan j).bounded a; omega⟩
  active := fun t j => Finset.univ.filter ((d.lifespan j).active t.val)
  initial := fun j => markedMemoryFiniteList_ofList (d.lifespan j).initial (d.lifespan j).initial_nodup
  births := fun v j => markedMemoryFiniteList_ofList ((d.lifespan j).births (2*v.val))
    ((d.lifespan j).ghost_nodup (2*v.val) (by have h := v.isLt; omega) (by omega))
  incoming := fun v j => (d.lifespan j).incoming (2*v.val+1)
  outgoing := fun v j => (d.lifespan j).outgoing (2*v.val+1)
  position := fun v => d.position v.val
  activeId := fun v => d.activeId v.val
  particle := d.particle

@[simp] theorem markedMemoryFiniteData_first (j : J) (a : A j) :
    (markedMemoryFiniteData_ofIndependent hZ d).firstAt j a=(d.lifespan j).first a := rfl

@[simp] theorem markedMemoryFiniteData_last (j : J) (a : A j) :
    (markedMemoryFiniteData_ofIndependent hZ d).lastAt j a=(d.lifespan j).last a := rfl

theorem markedMemoryFiniteData_active (t : ℕ) (ht : t ≤ 2*n+1) (j : J) (a : A j) :
    (markedMemoryFiniteData_ofIndependent hZ d).activeAt t j a ↔ (d.lifespan j).active t a := by
  have hlt : t<2*n+2 := by omega
  simp [MarkedMemoryFiniteTableauData.activeAt,hlt,markedMemoryFiniteData_ofIndependent]

@[simp] theorem markedMemoryFiniteData_initial (j : J) :
    (markedMemoryFiniteData_ofIndependent hZ d).initialAt j=(d.lifespan j).initial := by
  simp [MarkedMemoryFiniteTableauData.initialAt,markedMemoryFiniteData_ofIndependent]

theorem markedMemoryFiniteData_births (v : ℕ) (hv : v ≤ n) (j : J) :
    (markedMemoryFiniteData_ofIndependent hZ d).birthsAt (2*v) j=(d.lifespan j).births (2*v) := by
  have hh := MarkedMemoryFiniteTableauData.birthsAt_valid
    (markedMemoryFiniteData_ofIndependent hZ d) (⟨v,by omega⟩ : Fin (n+1)) j
  simpa only [markedMemoryFiniteData_ofIndependent,markedMemoryFiniteList_toList_ofList] using hh

theorem markedMemoryFiniteData_births_stage (t : ℕ) (ht : t<2*n+1) (he : t%2=0) (j : J) :
    (markedMemoryFiniteData_ofIndependent hZ d).birthsAt t j=(d.lifespan j).births t := by
  have hv : t/2≤n := by omega
  have hh : 2*(t/2)=t := by omega
  simpa only [hh] using markedMemoryFiniteData_births hZ d (t/2) hv j

theorem markedMemoryFiniteData_incoming (v : ℕ) (hv : v<n) (j : J) :
    (markedMemoryFiniteData_ofIndependent hZ d).incomingAt (2*v+1) j=(d.lifespan j).incoming (2*v+1) := by
  have hh := MarkedMemoryFiniteTableauData.incomingAt_valid
    (markedMemoryFiniteData_ofIndependent hZ d) (⟨v,hv⟩ : Fin n) j
  exact hh

theorem markedMemoryFiniteData_outgoing (v : ℕ) (hv : v<n) (j : J) :
    (markedMemoryFiniteData_ofIndependent hZ d).outgoingAt (2*v+1) j=(d.lifespan j).outgoing (2*v+1) := by
  have hh := MarkedMemoryFiniteTableauData.outgoingAt_valid
    (markedMemoryFiniteData_ofIndependent hZ d) (⟨v,hv⟩ : Fin n) j
  exact hh

theorem markedMemoryFiniteData_incoming_stage (t : ℕ) (ht : t<2*n+1) (he : t%2=1) (j : J) :
    (markedMemoryFiniteData_ofIndependent hZ d).incomingAt t j=(d.lifespan j).incoming t := by
  have hv : t/2<n := by omega
  have hh : 2*(t/2)+1=t := by omega
  simpa only [hh] using markedMemoryFiniteData_incoming hZ d (t/2) hv j

theorem markedMemoryFiniteData_outgoing_stage (t : ℕ) (ht : t<2*n+1) (he : t%2=1) (j : J) :
    (markedMemoryFiniteData_ofIndependent hZ d).outgoingAt t j=(d.lifespan j).outgoing t := by
  have hv : t/2<n := by omega
  have hh : 2*(t/2)+1=t := by omega
  simpa only [hh] using markedMemoryFiniteData_outgoing hZ d (t/2) hv j

theorem markedMemoryFiniteData_position (v : ℕ) (hv : v≤n) :
    (markedMemoryFiniteData_ofIndependent hZ d).positionAt v=d.position v := by
  exact MarkedMemoryFiniteTableauData.positionAt_valid
    (markedMemoryFiniteData_ofIndependent hZ d) (⟨v,by omega⟩ : Fin (n+1))

theorem markedMemoryFiniteData_activeId (v : ℕ) (hv : v≤n) (j : J) :
    (markedMemoryFiniteData_ofIndependent hZ d).activeIdAt v j=d.activeId v j := by
  exact MarkedMemoryFiniteTableauData.activeIdAt_valid
    (markedMemoryFiniteData_ofIndependent hZ d) (⟨v,by omega⟩ : Fin (n+1)) j

@[simp] theorem markedMemoryFiniteData_particle (j : J) (a : A j) :
    (markedMemoryFiniteData_ofIndependent hZ d).particle j a=d.particle j a := rfl

theorem markedMemoryFiniteData_pending (t : ℕ) (ht : t≤2*n+1) (j : J) :
    (markedMemoryFiniteData_ofIndependent hZ d).pendingAt t j=
      markedMemoryPendingIdentitySet (d.lifespan j) t := by
  ext a
  simp [MarkedMemoryFiniteTableauData.pendingAt,markedMemoryPendingIdentitySet,
    markedMemoryFiniteData_active hZ d t ht]

end
end ArtinMatthews
