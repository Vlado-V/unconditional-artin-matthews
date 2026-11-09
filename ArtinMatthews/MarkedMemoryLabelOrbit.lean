module

public import ArtinMatthews.MarkedMemoryIndependentRelabel
public import ArtinMatthews.MarkedMemoryIndependentPopulation


set_option backward.privateInPublic true
@[expose] public section

/-! Every supplied identity actually occurs in a finite active/pending
population. Hence per-band relabeling is free on a fixed tableau.
This orbit statement does not identify an unrestricted assembly fiber. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)} {n : ℕ}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

theorem markedMemoryIndependent_label_used (j : J) (a : A j) :
    ∃ t ≤ 2*n+1,(∃ k,d.activeId (t/2) j k=a) ∨ a ∈ markedMemoryIndependentQueue hZ d t j := by
  let t := (d.lifespan j).first a
  have ht : t≤2*n+1 := ((d.lifespan j).nonempty a).trans ((d.lifespan j).bounded a)
  refine ⟨t,ht,?_⟩
  by_cases ha : (d.lifespan j).active t a
  · exact Or.inl ((markedMemoryIndependentActive_mem hZ d t ht j a).mp ha)
  · exact Or.inr ((markedMemoryPendingQueueAt_mem (d.lifespan j) t ht a).mpr
      ⟨le_rfl,(d.lifespan j).nonempty a,ha⟩)

theorem markedMemoryIndependent_labelMap_ext (e f : (j : J) → A j → A j)
    (hactive : ∀ v,v≤n → ∀ j k,e j (d.activeId v j k)=f j (d.activeId v j k))
    (hqueue : ∀ t,t≤2*n+1 → ∀ j,
      (markedMemoryIndependentQueue hZ d t j).map (e j)=(markedMemoryIndependentQueue hZ d t j).map (f j)) :
    e=f := by
  funext j a
  obtain ⟨t,ht,ha | ha⟩ := markedMemoryIndependent_label_used hZ d j a
  · obtain ⟨k,rfl⟩ := ha
    exact hactive (t/2) (by omega) j k
  · exact List.map_inj_left.mp (hqueue t ht j) a ha

theorem markedMemoryIndependentRelabel_orbit_injective :
    Function.Injective (fun e : (j : J) → Equiv.Perm (A j) => markedMemoryIndependentRelabel hZ e d) := by
  intro e f h
  have he : (fun j => (e j : A j → A j))=(fun j => (f j : A j → A j)) := by
    apply markedMemoryIndependent_labelMap_ext hZ d
    · intro v _ j k
      exact congrArg (fun z : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n =>
        z.activeId v j k) h
    · intro t _ j
      have hh := congrArg (fun z : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n =>
        markedMemoryIndependentQueue hZ z t j) h
      simpa only [markedMemoryIndependentRelabel_queue] using hh
  funext j
  exact Equiv.ext (fun a => congrFun (congrFun he j) a)

def markedMemoryIndependentLabelOrbit :=
  Set.range (fun e : (j : J) → Equiv.Perm (A j) => markedMemoryIndependentRelabel hZ e d)

def markedMemoryIndependentLabelOrbitEquiv :
    ((j : J) → Equiv.Perm (A j)) ≃ markedMemoryIndependentLabelOrbit hZ d :=
  Equiv.ofInjective _ (markedMemoryIndependentRelabel_orbit_injective hZ d)

instance markedMemoryIndependentLabelOrbit_fintype :
    Fintype (markedMemoryIndependentLabelOrbit hZ d) :=
  Fintype.ofEquiv ((j : J) → Equiv.Perm (A j)) (markedMemoryIndependentLabelOrbitEquiv hZ d)

theorem markedMemoryIndependentLabelOrbit_card :
    Fintype.card (markedMemoryIndependentLabelOrbit hZ d)=∏ j,(Fintype.card (A j)).factorial := by
  rw [← Fintype.card_congr (markedMemoryIndependentLabelOrbitEquiv hZ d)]
  simp only [Fintype.card_pi,Fintype.card_perm]

theorem markedMemoryIndependentLabelOrbit_sum {R : Type*} [AddCommMonoid R]
    (F : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n → R) :
    (∑ e : (j : J) → Equiv.Perm (A j),F (markedMemoryIndependentRelabel hZ e d)) =
      ∑ z : markedMemoryIndependentLabelOrbit hZ d,F z.1 :=
  Equiv.sum_comp (markedMemoryIndependentLabelOrbitEquiv hZ d) (fun z => F z.1)

end
end ArtinMatthews
