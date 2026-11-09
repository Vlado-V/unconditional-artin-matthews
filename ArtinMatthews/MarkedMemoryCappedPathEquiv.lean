module

public import ArtinMatthews.MarkedMemoryCappedPathInjective
public import ArtinMatthews.MarkedMemoryActualCappedLift


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite capped path/decorations carrier is equivalent to
the supported original history carrier. Canonical used-prime labels
give exactly one preimage, rather than an assumed labeling quotient. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (hP : ∀ i j,i≠j → Disjoint (P i) (P j))
  (s : MarkedRawState P (pads+1) B Z) (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)

def markedMemoryCappedPathEquiv :
    MarkedMemoryCappedPathDecoratedIndex (n := n) hZ s ≃ MarkedMemoryPrimeSupportedHistory (n := n) hZ s :=
  Equiv.ofBijective (markedMemoryCappedPathSupportedAssembly hZ hP s)
    ⟨fun _ _ h => markedMemoryCappedPathDecoratedAssembly_injective hZ hP s hempty (congrArg Subtype.val h),
      markedMemoryCappedPathSupportedAssembly_surjective hZ s hempty hP⟩

theorem markedMemoryCappedPathEquiv_apply
    (i : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ s) :
    (markedMemoryCappedPathEquiv hZ hP s hempty i).1=markedMemoryCappedPathDecoratedAssembly hZ hP s i := rfl

include hempty in
theorem markedMemoryCappedPath_actual_fiber_card
    (H : MarkedMemoryPrimeSupportedHistory (n := n) hZ s) :
    Fintype.card {i : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ s //
      markedMemoryCappedPathDecoratedAssembly hZ hP s i=H.1}=1 := by
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨⟨markedMemoryActualCappedLift hZ s hempty H,
    markedMemoryActualCappedLift_reconstruction hZ s hempty hP H⟩,?_⟩
  intro i
  apply Subtype.ext
  apply markedMemoryCappedPathDecoratedAssembly_injective hZ hP s hempty
  exact i.2.trans (markedMemoryActualCappedLift_reconstruction hZ s hempty hP H).symm

include hempty in
theorem markedMemoryCappedPath_supported_sum {R : Type*} [AddCommMonoid R]
    (F : MarkedMemoryChronologicalHistory hZ n s → R) :
    (∑ H : MarkedMemoryPrimeSupportedHistory (n := n) hZ s,F H.1)=
      ∑ i : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ s,
        F (markedMemoryCappedPathDecoratedAssembly hZ hP s i) :=
  (Equiv.sum_comp (markedMemoryCappedPathEquiv hZ hP s hempty) (fun H => F H.1)).symm

end
end ArtinMatthews
