module

public import ArtinMatthews.MarkedMemoryFiniteTableau
public import ArtinMatthews.MarkedMemoryIndependentHistory


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine finite index for decorated lifespan histories at a fixed
raw source. It stores finite local data, a proved source match and copied
slot order, but no original history or image-coverage premise. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)

abbrev MarkedMemoryFiniteHistoryIndex :=
  {d : MarkedMemoryFiniteTableau (A := A) (P := P) (pads := pads) (B := B) hZ n //
    markedMemoryIndependentState hZ (markedMemoryFiniteTableau_toIndependent hZ d) 0 (Nat.zero_le n) = s} ×
      (Fin n → J → Equiv.Perm (Fin pads))

instance markedMemoryFiniteHistoryIndex_fintype : Fintype (MarkedMemoryFiniteHistoryIndex (A := A) (n := n) hZ s) := by
  infer_instance

def markedMemoryFiniteHistoryAssembly (index : MarkedMemoryFiniteHistoryIndex (A := A) (n := n) hZ s) :
    MarkedMemoryChronologicalHistory hZ n s :=
  markedMemoryHistoryTransport hZ index.1.2
    (markedMemoryIndependentHistory hZ (markedMemoryFiniteTableau_toIndependent hZ index.1.1) index.2)

/-- Keep every actual fiber of the finite decorated-tableau assembly.
This identity introduces no unproved claim about its multiplicity. -/
theorem markedMemoryFiniteHistoryAssembly_fiber_sum {R : Type*} [AddCommMonoid R]
    (F : MarkedMemoryChronologicalHistory hZ n s → R) :
    (∑ index : MarkedMemoryFiniteHistoryIndex (A := A) (n := n) hZ s,
      F (markedMemoryFiniteHistoryAssembly hZ s index)) =
    ∑ history : MarkedMemoryChronologicalHistory hZ n s,
      ∑ _index : {index : MarkedMemoryFiniteHistoryIndex (A := A) (n := n) hZ s //
        markedMemoryFiniteHistoryAssembly hZ s index = history}, F history := by
  have he := Fintype.sum_fiberwise (markedMemoryFiniteHistoryAssembly (A := A) (n := n) hZ s)
    (fun index => F (markedMemoryFiniteHistoryAssembly hZ s index))
  refine he.symm.trans ?_
  apply Finset.sum_congr rfl
  intro history _
  apply Finset.sum_congr rfl
  intro index _
  exact congrArg F index.property

end
end ArtinMatthews
