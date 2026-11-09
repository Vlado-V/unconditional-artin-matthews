module

public import ArtinMatthews.MarkedMemoryIndependentHistory
public import ArtinMatthews.MarkedRawBoundary


set_option backward.privateInPublic true
@[expose] public section

/-! Nonzero literal terminal boundary forces the independent terminal
queues to be empty. This is extracted from the actual raw target, not
supplied as a primewise endpoint condition. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (order : Fin n → J → Equiv.Perm (Fin pads)) (z₀ : Z)

local notation "H" => markedMemoryIndependentHistory hZ d order

theorem markedMemoryIndependent_terminal_queue_of_boundary_ne_zero
    (hb : markedRawBoundary z₀ (markedMemoryChronologicalTarget hZ H)≠0) (j : J) :
    markedMemoryIndependentQueue hZ d (2*n+1) j=[] := by
  have he : (markedMemoryChronologicalTarget hZ H).2.2=markedRawBoundaryEmptyMemory P B := by
    by_contra hn
    apply hb
    simp only [markedRawBoundary,hn,and_false,ite_false]
  have ht := congrArg (fun u : MarkedRawState P (pads+1) B Z => u.2.2)
    (markedMemoryIndependentHistory_target hZ d order)
  have hm : markedMemoryIndependentMemory hZ d (2*n+1) (by omega)=markedRawBoundaryEmptyMemory P B :=
    ht.symm.trans he
  have hl := congrArg (fun m : MarkedRawMemory P B => List.ofFn (m.2 j)) hm
  rw [markedMemoryIndependentMemory,markedMemoryLabeledQueueState_list] at hl
  change (markedMemoryIndependentQueue hZ d (2*n+1) j).map (d.particle j)=[] at hl
  exact List.map_eq_nil_iff.mp hl

end
end ArtinMatthews
