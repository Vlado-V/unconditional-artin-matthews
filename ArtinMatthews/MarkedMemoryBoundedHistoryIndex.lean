module

public import ArtinMatthews.MarkedMemoryFiniteHistoryIndex


set_option backward.privateInPublic true
@[expose] public section

/-! One finite decorated-history index, allowing every band-label count
up to a fixed bound. Each label family is Fin(N_j), so no history-dependent
type family is hidden in the summation domain. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z) (K : ℕ)

abbrev MarkedMemoryBoundedHistoryIndex :=
  Σ counts : J → Fin (K+1),
    MarkedMemoryFiniteHistoryIndex (A := fun j => Fin (counts j : ℕ)) (n := n) hZ s

instance markedMemoryBoundedHistoryIndex_fintype :
    Fintype (MarkedMemoryBoundedHistoryIndex (n := n) hZ s K) := by
  infer_instance

def markedMemoryBoundedHistoryAssembly
    (index : MarkedMemoryBoundedHistoryIndex (n := n) hZ s K) : MarkedMemoryChronologicalHistory hZ n s :=
  markedMemoryFiniteHistoryAssembly hZ s index.2

theorem markedMemoryBoundedHistoryAssembly_fiber_sum {R : Type*} [AddCommMonoid R]
    (F : MarkedMemoryChronologicalHistory hZ n s → R) :
    (∑ index : MarkedMemoryBoundedHistoryIndex (n := n) hZ s K,
      F (markedMemoryBoundedHistoryAssembly hZ s K index)) =
    ∑ history : MarkedMemoryChronologicalHistory hZ n s,
      ∑ _index : {index : MarkedMemoryBoundedHistoryIndex (n := n) hZ s K //
        markedMemoryBoundedHistoryAssembly hZ s K index = history}, F history := by
  have he := Fintype.sum_fiberwise (markedMemoryBoundedHistoryAssembly (n := n) hZ s K)
    (fun index => F (markedMemoryBoundedHistoryAssembly hZ s K index))
  refine he.symm.trans ?_
  apply Finset.sum_congr rfl
  intro history _
  apply Finset.sum_congr rfl
  intro index _
  exact congrArg F index.property

end
end ArtinMatthews
