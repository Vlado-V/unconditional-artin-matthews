module

public import ArtinMatthews.MarkedMinorArcRawEdgePatternColumn
public import ArtinMatthews.MarkedMinorArcRawEdgeSlotTranspose


set_option backward.privateInPublic true
@[expose] public section

/-! Exact two-sided slot symmetrization of the literal restricted edge. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

def markedRawEdgePatternSymmetrized {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (A : MarkedRawEdgePatternKernel P pads B Z)
    (f : MarkedRawState P (pads+1) B Z → ℂ) :=
  markedRawSlotAverage (markedRawEdgePatternApply ν δ γ hZ A (markedRawSlotAverage f))

theorem markedRawEdgePatternSymmetrized_transpose
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (A : MarkedRawEdgePatternKernel P pads B Z)
    (hAl : ∀ p q z active target, MarkedRawMemorySymmetric (fun m => A p q (z,(active,m)) target))
    (hAr : ∀ p q source z active, MarkedRawMemorySymmetric (fun m => A p q source (z,(active,m))))
    (f g : MarkedRawState P (pads+1) B Z → ℂ)
    (hf : ∀ z active, MarkedRawMemorySymmetric (fun m => f (z,(active,m))))
    (hg : ∀ z active, MarkedRawMemorySymmetric (fun m => g (z,(active,m)))) :
    (∑ s, (markedRawStateMass ν s : ℂ) * g s * markedRawEdgePatternSymmetrized ν δ γ hZ A f s) =
      ∑ s, (markedRawStateMass ν s : ℂ) * f s *
        markedRawEdgePatternSymmetrized ν γ δ hZ (markedRawEdgePatternReverse A) g s := by
  unfold markedRawEdgePatternSymmetrized
  rw [markedRawSlotAverage_transpose]
  have ht := markedRawEdgePatternApply_transpose ν δ γ hZ A hAl hAr
    (markedRawSlotAverage f) (markedRawSlotAverage g)
    (markedRawSlotAverage_symmetric f hf) (markedRawSlotAverage_symmetric g hg)
  calc
    _ = ∑ s, (markedRawStateMass ν s : ℂ) * markedRawSlotAverage g s *
        markedRawEdgePatternApply ν δ γ hZ A (markedRawSlotAverage f) s := by
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = _ := ht
    _ = ∑ s, (markedRawStateMass ν s : ℂ) *
        markedRawEdgePatternApply ν γ δ hZ (markedRawEdgePatternReverse A) (markedRawSlotAverage g) s *
        markedRawSlotAverage f s := by
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = _ := (markedRawSlotAverage_transpose ν
      (markedRawEdgePatternApply ν γ δ hZ (markedRawEdgePatternReverse A) (markedRawSlotAverage g)) f).symm

theorem markedRawSlotAverageReal_integral
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} (F : MarkedRawState P M B Z → ℝ) :
    (∑ s, markedRawStateMass ν s * markedRawSlotAverageReal F s) =
      ∑ s, markedRawStateMass ν s * F s := by
  have h := markedRawSlotAverage_weighted_invariant ν (fun _ => 1) F (fun _ _ => rfl)
  simpa only [mul_one] using h.symm

end
end ArtinMatthews
