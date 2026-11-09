module

public import ArtinMatthews.MarkedMemoryFiniteTableauRecovery


set_option backward.privateInPublic true
@[expose] public section

/-! The actual ordered ghost choice is unchanged by finite restriction
and canonical extension, including its deletion mask and birth order. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)} {n : ℕ}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

local notation "restored" => markedMemoryFiniteTableau_toIndependent hZ (markedMemoryIndependent_toFinite hZ d)

theorem markedMemoryFinite_restore_ghost_heq (v : ℕ) (hv : v≤n) :
    HEq (markedMemoryIndependentGhost hZ restored v hv) (markedMemoryIndependentGhost hZ d v hv) := by
  have hp := markedMemoryFinite_restore_position hZ d v hv
  have ha : (fun j k => ((restored).particle j ((restored).activeId v j k)).1)=
      (fun j k => (d.particle j (d.activeId v j k)).1) := by
    funext j k
    rw [markedMemoryFinite_restore_particle,markedMemoryFinite_restore_activeId hZ d v hv j]
  have hq : markedMemoryIndependentQueue hZ restored (2*v)=markedMemoryIndependentQueue hZ d (2*v) :=
    funext (markedMemoryFinite_restore_queue hZ d (2*v) (by omega))
  have hb : (fun j => ((restored).lifespan j).births (2*v))=(fun j => (d.lifespan j).births (2*v)) :=
    funext (markedMemoryFinite_restore_births hZ d v hv)
  have hl : (fun j => ((restored).lifespan j).last)=(fun j => (d.lifespan j).last) := rfl
  have ht : (restored).particle=d.particle := rfl
  unfold markedMemoryIndependentGhost
  congr 1 <;> first | assumption | rfl | exact proof_irrel_heq _ _

end
end ArtinMatthews
