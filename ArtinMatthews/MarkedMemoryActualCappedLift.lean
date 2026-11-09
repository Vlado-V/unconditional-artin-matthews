module

public import ArtinMatthews.MarkedMemoryActualCappedPrerequisites
public import ArtinMatthews.MarkedMemoryIndependentCappedLift


set_option backward.privateInPublic true
@[expose] public section

/-! Every actual supported history has a computed capped path with its
original birth and copied-slot decorations. The reconstructed history
is exactly the input history. No image-coverage premise is supplied. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (s : MarkedRawState P (pads+1) B Z) (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)

def markedMemoryActualCappedLift
    (H : MarkedMemoryPrimeSupportedHistory (n := n) hZ s) :
    MarkedMemoryCappedPathDecoratedIndex (n := n) hZ s :=
  markedMemoryIndependentCappedLift hZ (markedMemoryActualTableau hZ H.1 H.2.1)
    (markedMemoryActualCapped_prime_injective hZ H.1 H.2.1 hempty H.2.2.1)
    (markedMemoryActualCapped_initial hZ H.1 H.2.1 hempty)
    (markedMemoryActualCapped_terminal hZ H.1 H.2.1 H.2.2.2)
    (markedMemoryActualTableau_birthNormalized hZ H.1 hempty H.2.1)
    (markedMemoryActualOrder hZ H.1 H.2.1)
    (markedMemoryActualCapped_anchor hZ H.1 H.2.1) s
    (markedMemoryActualTableau_initial hZ H.1 H.2.1)

theorem markedMemoryActualCappedLift_reconstruction
    (hP : ∀ i j,i≠j → Disjoint (P i) (P j))
    (H : MarkedMemoryPrimeSupportedHistory (n := n) hZ s) :
    markedMemoryCappedPathDecoratedAssembly hZ hP s (markedMemoryActualCappedLift hZ s hempty H)=H.1 := by
  have hi := markedMemoryIndependentCappedLift_history hZ (markedMemoryActualTableau hZ H.1 H.2.1)
    (markedMemoryActualCapped_prime_injective hZ H.1 H.2.1 hempty H.2.2.1)
    (markedMemoryActualCapped_initial hZ H.1 H.2.1 hempty)
    (markedMemoryActualCapped_terminal hZ H.1 H.2.1 H.2.2.2)
    (markedMemoryActualTableau_birthNormalized hZ H.1 hempty H.2.1)
    (markedMemoryActualOrder hZ H.1 H.2.1)
    (markedMemoryActualCapped_anchor hZ H.1 H.2.1) s
    (markedMemoryActualTableau_initial hZ H.1 H.2.1) hP
  exact hi.trans (markedMemoryActualHistory_reconstruction hZ H.1 H.2.1)

include hempty in
theorem markedMemoryCappedPathSupportedAssembly_surjective
    (hP : ∀ i j,i≠j → Disjoint (P i) (P j)) :
    Function.Surjective (markedMemoryCappedPathSupportedAssembly (n := n) hZ hP s) := by
  intro H
  refine ⟨markedMemoryActualCappedLift hZ s hempty H,?_⟩
  apply Subtype.ext
  exact markedMemoryActualCappedLift_reconstruction hZ s hempty hP H

end
end ArtinMatthews
