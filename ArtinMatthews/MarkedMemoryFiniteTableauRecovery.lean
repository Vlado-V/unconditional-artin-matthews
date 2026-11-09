module

public import ArtinMatthews.MarkedMemoryFiniteTableauRestriction


set_option backward.privateInPublic true
@[expose] public section

/-! The finite restriction and canonical extension recover every
meaningful queue and physical state of the original independent data. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)} {n : ℕ}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

local notation "restored" => markedMemoryFiniteTableau_toIndependent hZ (markedMemoryIndependent_toFinite hZ d)

omit [∀ j,DecidableEq (A j)] in
@[simp] theorem markedMemoryFinite_restore_first (j : J) (a : A j) :
    ((restored).lifespan j).first a=(d.lifespan j).first a := rfl

omit [∀ j,DecidableEq (A j)] in
@[simp] theorem markedMemoryFinite_restore_last (j : J) (a : A j) :
    ((restored).lifespan j).last a=(d.lifespan j).last a := rfl

omit [∀ j,DecidableEq (A j)] in
@[simp] theorem markedMemoryFinite_restore_particle (j : J) (a : A j) :
    (restored).particle j a=d.particle j a := rfl

omit [∀ j,DecidableEq (A j)] in
theorem markedMemoryFinite_restore_active (t : ℕ) (ht : t≤2*n+1) (j : J) (a : A j) :
    ((restored).lifespan j).active t a ↔ (d.lifespan j).active t a :=
  markedMemoryFiniteData_active hZ d t ht j a

omit [∀ j,DecidableEq (A j)] in
theorem markedMemoryFinite_restore_position (v : ℕ) (hv : v≤n) :
    (restored).position v=d.position v := markedMemoryFiniteData_position hZ d v hv

omit [∀ j,DecidableEq (A j)] in
theorem markedMemoryFinite_restore_activeId (v : ℕ) (hv : v≤n) (j : J) :
    (restored).activeId v j=d.activeId v j := markedMemoryFiniteData_activeId hZ d v hv j

omit [∀ j,DecidableEq (A j)] in
theorem markedMemoryFinite_restore_births (v : ℕ) (hv : v≤n) (j : J) :
    ((restored).lifespan j).births (2*v)=(d.lifespan j).births (2*v) :=
  markedMemoryFiniteData_births hZ d v hv j

omit [∀ j,DecidableEq (A j)] in
theorem markedMemoryFinite_restore_incoming (v : ℕ) (hv : v<n) (j : J) :
    ((restored).lifespan j).incoming (2*v+1)=(d.lifespan j).incoming (2*v+1) :=
  markedMemoryFiniteData_incoming hZ d v hv j

omit [∀ j,DecidableEq (A j)] in
theorem markedMemoryFinite_restore_outgoing (v : ℕ) (hv : v<n) (j : J) :
    ((restored).lifespan j).outgoing (2*v+1)=(d.lifespan j).outgoing (2*v+1) :=
  markedMemoryFiniteData_outgoing hZ d v hv j

theorem markedMemoryFinite_restore_queue (t : ℕ) (ht : t≤2*n+1) (j : J) :
    markedMemoryIndependentQueue hZ restored t j=markedMemoryIndependentQueue hZ d t j := by
  change markedMemoryPendingQueueAt ((restored).lifespan j) t=markedMemoryPendingQueueAt (d.lifespan j) t
  induction t with
  | zero => exact markedMemoryFiniteData_initial hZ d j
  | succ t ih =>
    have hi := ih (by omega)
    simp only [markedMemoryPendingQueueAt]
    by_cases he : t%2=0
    · simp only [he,ite_true,hi]
      change markedMemoryGhostQueue _ ((markedMemoryFiniteData_ofIndependent hZ d).birthsAt t j)
        (fun a => (d.lifespan j).last a) t= _
      rw [markedMemoryFiniteData_births_stage hZ d t (by omega) he j]
    · have ho : t%2=1 := by omega
      simp only [he,ite_false,hi]
      change markedMemoryEdgeQueue _ ((markedMemoryFiniteData_ofIndependent hZ d).incomingAt t j)
        ((markedMemoryFiniteData_ofIndependent hZ d).outgoingAt t j)
        (decide (t < (d.lifespan j).last ((markedMemoryFiniteData_ofIndependent hZ d).outgoingAt t j)))= _
      rw [markedMemoryFiniteData_incoming_stage hZ d t (by omega) ho j,
        markedMemoryFiniteData_outgoing_stage hZ d t (by omega) ho j]

theorem markedMemoryFinite_restore_memory (t : ℕ) (ht : t≤2*n+1) :
    markedMemoryIndependentMemory hZ restored t ht=markedMemoryIndependentMemory hZ d t ht := by
  unfold markedMemoryIndependentMemory
  apply markedMemoryState_eq_of_lists
  intro j
  rw [markedMemoryLabeledQueueState_list,markedMemoryLabeledQueueState_list,
    markedMemoryFinite_restore_queue hZ d t ht j]
  rfl

theorem markedMemoryFinite_restore_state (v : ℕ) (hv : v≤n) :
    markedMemoryIndependentState hZ restored v hv=markedMemoryIndependentState hZ d v hv := by
  unfold markedMemoryIndependentState
  rw [markedMemoryFinite_restore_memory hZ d (2*v) (by omega),
    markedMemoryFinite_restore_position hZ d v hv]
  have hid : (restored).activeId v=d.activeId v := funext (markedMemoryFinite_restore_activeId hZ d v hv)
  rw [hid]
  rfl

theorem markedMemoryFinite_restore_postGhost (v : ℕ) (hv : v≤n) :
    markedMemoryIndependentPostGhost hZ restored v hv=markedMemoryIndependentPostGhost hZ d v hv := by
  unfold markedMemoryIndependentPostGhost
  rw [markedMemoryFinite_restore_memory hZ d (2*v+1) (by omega),
    markedMemoryFinite_restore_position hZ d v hv]
  have hid : (restored).activeId v=d.activeId v := funext (markedMemoryFinite_restore_activeId hZ d v hv)
  rw [hid]
  rfl

end
end ArtinMatthews
