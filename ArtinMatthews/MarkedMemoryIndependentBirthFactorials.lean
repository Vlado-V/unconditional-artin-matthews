module

public import ArtinMatthews.MarkedMemoryIndependentScalarEvents


set_option backward.privateInPublic true
@[expose] public section

/-! The independent ordered ghost-birth lists give exactly the original
factorial denominator at every chronological vertex. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  {A : J → Type*} [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)]
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (order : Fin n → J → Equiv.Perm (Fin pads))

def markedMemoryIndependentBirthFactorials : ℝ :=
  ∏ v : Fin (n+1), ∏ j : J, (((d.lifespan j).births (2*v.val)).length.factorial : ℝ)

theorem markedMemoryIndependent_birthFactorials :
    markedMemoryHistoryBirthFactorials hZ (markedMemoryIndependentHistory hZ d order) =
      markedMemoryIndependentBirthFactorials hZ d := by
  unfold markedMemoryHistoryBirthFactorials markedMemoryIndependentBirthFactorials
  apply Finset.prod_congr rfl
  intro v _
  unfold markedMemoryGhostBirthFactorial
  apply Finset.prod_congr rfl
  intro j _
  have hs := markedMemoryGhostSizeEq hZ (markedMemoryIndependent_vertex_state hZ d order v) _ _
    (markedMemoryIndependent_vertex_ghost_heq hZ d order v) j
  exact congrArg (fun m : ℕ => (m.factorial : ℝ)) hs

end
end ArtinMatthews
