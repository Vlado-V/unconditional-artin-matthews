module

public import ArtinMatthews.MarkedMemoryLifespanBoundaryParity
public import ArtinMatthews.MarkedMemoryIndependentLifespans


set_option backward.privateInPublic true
@[expose] public section

/-! Active visits and parity recover the genuine endpoint interval of
an independent identity with empty initial and terminal queues. The
first/last active visits are derived from local incidence and boundary
laws, without an assumed primewise correspondence. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

def markedMemoryIndependentIdentityVisits (j : J) (a : A j) : Finset (Fin (n+1)) :=
  Finset.univ.filter (fun v => (d.lifespan j).active (2*v.val) a)

omit [∀ j,DecidableEq (A j)] in
theorem markedMemoryIndependentIdentityVisits_mem (j : J) (a : A j) (v : Fin (n+1)) :
    v∈markedMemoryIndependentIdentityVisits hZ d j a ↔ (d.lifespan j).active (2*v.val) a := by
  simp only [markedMemoryIndependentIdentityVisits,Finset.mem_filter,Finset.mem_univ,true_and]

omit [∀ j,DecidableEq (A j)] in
theorem markedMemoryIndependentIdentityVisits_alive (j : J) (a : A j) (v : Fin (n+1))
    (hv : v∈markedMemoryIndependentIdentityVisits hZ d j a) :
    (d.lifespan j).first a≤2*v.val ∧ 2*v.val+1≤(d.lifespan j).last a := by
  obtain ⟨k,hk⟩ := (d.active_mem v.val (by omega) j a).mp
    ((markedMemoryIndependentIdentityVisits_mem hZ d j a v).mp hv)
  simpa only [hk] using d.active_alive v.val (by omega) j k

omit [∀ j,DecidableEq (A j)] in
theorem markedMemoryIndependentIdentityVisits_first_even
    (hempty : ∀ j,(d.lifespan j).initial=[])
    (j : J) (a : A j) (he : (d.lifespan j).first a%2=0) :
    ∃ v∈markedMemoryIndependentIdentityVisits hZ d j a,(d.lifespan j).first a=2*v.val := by
  have hf := (d.lifespan j).nonempty a
  have hl := (d.lifespan j).bounded a
  let v : Fin (n+1) := ⟨(d.lifespan j).first a/2,by omega⟩
  have ht : (d.lifespan j).first a=2*v.val := by dsimp [v]; omega
  refine ⟨v,?_,ht⟩
  apply (markedMemoryIndependentIdentityVisits_mem hZ d j a v).mpr
  rw [← ht]
  exact markedMemoryLifespan_first_even_active (d.lifespan j) (hempty j) a he

theorem markedMemoryIndependentIdentityVisits_last_odd
    (hempty : ∀ j,markedMemoryIndependentQueue hZ d (2*n+1) j=[])
    (j : J) (a : A j) (ho : (d.lifespan j).last a%2=1) :
    ∃ v∈markedMemoryIndependentIdentityVisits hZ d j a,(d.lifespan j).last a=2*v.val+1 := by
  have hl := (d.lifespan j).bounded a
  let v : Fin (n+1) := ⟨(d.lifespan j).last a/2,by omega⟩
  have ht : (d.lifespan j).last a=2*v.val+1 := by dsimp [v]; omega
  refine ⟨v,?_,ht⟩
  apply (markedMemoryIndependentIdentityVisits_mem hZ d j a v).mpr
  apply ((d.lifespan j).ghost_active (2*v.val) (by omega) (by omega) a).mp
  rw [← ht]
  exact markedMemoryLifespan_last_odd_active (d.lifespan j) (hempty j) a ho

end
end ArtinMatthews
