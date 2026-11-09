module

public import ArtinMatthews.MarkedMemoryFiniteTableauRestriction
public import ArtinMatthews.MarkedMemoryIndependentBirths


set_option backward.privateInPublic true
@[expose] public section

/-! All bounded queue decorations are recoverable from ordered pending
queues and active incidences. This extensionality lemma will be applied
to the actually derived address correspondence, not assumed on a fiber. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
  (d f : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

theorem markedMemoryIndependent_births_filter (v : ℕ) (hv : v≤n) (j : J) :
    (d.lifespan j).births (2*v)=
      (markedMemoryIndependentQueue hZ d (2*v+1) j).filter
        (fun a => decide ((d.lifespan j).first a=2*v+1)) := by
  have hq : markedMemoryIndependentQueue hZ d (2*v+1) j=
      (markedMemoryIndependentQueue hZ d (2*v) j).filter (fun a => decide (2*v<(d.lifespan j).last a)) ++
        (d.lifespan j).births (2*v) := by
    change markedMemoryPendingQueueAt (d.lifespan j) (2*v+1)=_
    simp only [markedMemoryPendingQueueAt,show (2*v)%2=0 by omega,ite_true,markedMemoryGhostQueue]
    rfl
  rw [hq,List.filter_append]
  have ho : ((markedMemoryIndependentQueue hZ d (2*v) j).filter
      (fun a => decide (2*v<(d.lifespan j).last a))).filter
        (fun a => decide ((d.lifespan j).first a=2*v+1))=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    have hmem := (List.mem_filter.mp ha).1
    have hf := ((markedMemoryPendingQueueAt_mem (d.lifespan j) (2*v) (by omega) a).mp hmem).1
    simp only [decide_eq_true_eq]
    omega
  have hb : ((d.lifespan j).births (2*v)).filter
      (fun a => decide ((d.lifespan j).first a=2*v+1))=(d.lifespan j).births (2*v) := by
    apply List.filter_eq_self.mpr
    intro a ha
    exact decide_eq_true (((d.lifespan j).ghost_births (2*v) (by omega) (by omega) a).mp ha).1
  rw [ho,hb,List.nil_append]

theorem markedMemoryIndependent_outgoing_eq_of_active
    (ha : ∀ t,t≤2*n+1 → ∀ j a,(d.lifespan j).active t a ↔ (f.lifespan j).active t a)
    (v : ℕ) (hv : v<n) (j : J) :
    (d.lifespan j).outgoing (2*v+1)=(f.lifespan j).outgoing (2*v+1) := by
  let a := (d.lifespan j).outgoing (2*v+1)
  have hd : (d.lifespan j).active (2*v+1) a := (d.lifespan j).edge_outgoing_active _ (by omega) (by omega)
  have hn : ¬(d.lifespan j).active (2*v+2) a := by
    intro h
    rcases ((d.lifespan j).edge_active (2*v+1) (by omega) (by omega) a).mp h with h | h
    · exact h.2 rfl
    · exact ((d.lifespan j).edge_distinct (2*v+1) (by omega) (by omega)) h.symm
  by_contra hne
  have hf : (f.lifespan j).active (2*v+2) a :=
    ((f.lifespan j).edge_active (2*v+1) (by omega) (by omega) a).mpr
      (Or.inl ⟨(ha _ (by omega) j a).mp hd,hne⟩)
  exact hn ((ha _ (by omega) j a).mpr hf)

theorem markedMemoryIndependent_incoming_eq_of_active
    (ha : ∀ t,t≤2*n+1 → ∀ j a,(d.lifespan j).active t a ↔ (f.lifespan j).active t a)
    (v : ℕ) (hv : v<n) (j : J) :
    (d.lifespan j).incoming (2*v+1)=(f.lifespan j).incoming (2*v+1) := by
  let a := (d.lifespan j).incoming (2*v+1)
  have hn : ¬(d.lifespan j).active (2*v+1) a := markedMemoryIndependentIncoming_not_active hZ d v hv j
  have hd : (d.lifespan j).active (2*v+2) a :=
    ((d.lifespan j).edge_active (2*v+1) (by omega) (by omega) a).mpr (Or.inr rfl)
  rcases ((f.lifespan j).edge_active (2*v+1) (by omega) (by omega) a).mp
      ((ha _ (by omega) j a).mp hd) with h | h
  · exact False.elim (hn ((ha _ (by omega) j a).mpr h.1))
  · exact h

theorem markedMemoryFinite_recovery_ext
    (hfirst : ∀ j a,(d.lifespan j).first a=(f.lifespan j).first a)
    (hlast : ∀ j a,(d.lifespan j).last a=(f.lifespan j).last a)
    (ha : ∀ t,t≤2*n+1 → ∀ j a,(d.lifespan j).active t a ↔ (f.lifespan j).active t a)
    (hpos : ∀ v,v≤n → d.position v=f.position v)
    (hid : ∀ v,v≤n → ∀ j,d.activeId v j=f.activeId v j)
    (hparticle : d.particle=f.particle)
    (hqueue : ∀ t,t≤2*n+1 → ∀ j,markedMemoryIndependentQueue hZ d t j=markedMemoryIndependentQueue hZ f t j) :
    markedMemoryIndependent_toFinite hZ d=markedMemoryIndependent_toFinite hZ f := by
  apply Subtype.ext
  apply MarkedMemoryFiniteTableauData.ext
  · funext j a
    apply Fin.ext
    exact hfirst j a
  · funext j a
    apply Fin.ext
    exact hlast j a
  · funext t j
    apply Finset.ext
    intro a
    simpa only [markedMemoryIndependent_toFinite,markedMemoryFiniteData_ofIndependent,
      Finset.mem_filter,Finset.mem_univ,true_and] using ha t (by have h:=t.isLt; omega) j a
  · funext j
    apply markedMemoryFiniteList_toList_injective
    simpa only [markedMemoryIndependent_toFinite,markedMemoryFiniteData_ofIndependent,
      markedMemoryFiniteList_toList_ofList,markedMemoryIndependentQueue,markedMemoryPendingQueueAt] using hqueue 0 (by omega) j
  · funext v j
    apply markedMemoryFiniteList_toList_injective
    simp only [markedMemoryIndependent_toFinite,markedMemoryFiniteData_ofIndependent,
      markedMemoryFiniteList_toList_ofList]
    rw [
      markedMemoryIndependent_births_filter hZ d v (by have h:=v.isLt; omega) j,
      markedMemoryIndependent_births_filter hZ f v (by have h:=v.isLt; omega) j,hqueue _ (by have h:=v.isLt; omega) j]
    simp only [hfirst]
  · funext v j
    exact markedMemoryIndependent_incoming_eq_of_active hZ d f ha v v.2 j
  · funext v j
    exact markedMemoryIndependent_outgoing_eq_of_active hZ d f ha v v.2 j
  · funext v
    exact hpos v (by have h:=v.isLt; omega)
  · funext v j
    exact hid v (by have h:=v.isLt; omega) j
  · exact hparticle

end
end ArtinMatthews
