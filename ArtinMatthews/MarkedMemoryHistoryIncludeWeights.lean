module

public import ArtinMatthews.MarkedMemoryHistoryIncludeValues
public import ArtinMatthews.MarkedMemoryBirthEventBoundary


set_option backward.privateInPublic true
@[expose] public section

/-! Exact naturality of the original signed geometric history weight and
literal source/terminal boundary term under position-window inclusion.
All prime masses, birth factorials, rho factors and slot probabilities
remain in their original coefficients. -/

namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z W : Finset (ℤ × ℤ)} (h : Z ⊆ W)
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (hW : ∀ z ∈ W, IsCoprime z.1 z.2)
  (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
  (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
  (χ : ℕ → MarkedRawState P (pads+1) B W → ℂ)

theorem markedMemoryGeometricEdgeChoiceInclude_weight (j : ℕ)
    (s : MarkedRawState P (pads+1) B Z) (c : MarkedMemoryEdgeChoice hZ s) :
    markedMemoryGeometricEdgeChoiceWeight ν V hW ψ η d₀ Y Q ρ orientation χ j
        (markedRawStateInclude h s) (markedMemoryEdgeChoiceInclude h hZ hW s c) =
      markedMemoryGeometricEdgeChoiceWeight ν V hZ ψ η d₀ Y Q ρ orientation
        (fun k s => χ k (markedRawStateInclude h s)) j s c := by
  unfold markedMemoryGeometricEdgeChoiceWeight
  split <;> exact markedMemoryEdgeChoiceInclude_weight h hZ hW ν V _ _ d₀ Y Q ρ _ s c

theorem markedMemoryHistoryInclude_geometricWeight (n j : ℕ)
    {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryGeometricHistoryWeight ν V hW ψ η d₀ Y Q ρ orientation qStage χ n j
        (markedMemoryHistoryInclude h hZ hW n H) =
      markedMemoryGeometricHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage
        (fun k s => χ k (markedRawStateInclude h s)) n j H := by
  induction n generalizing j s with
  | zero => exact markedMemoryGhostChoiceInclude_weight h hZ hW ν V (qStage j) ρ s H
  | succ n ih =>
    have hg := markedMemoryGhostChoiceInclude_weight h hZ hW ν V (qStage j) ρ s H.1
    have he := markedMemoryGeometricEdgeChoiceInclude_weight h hZ hW ν V ψ η d₀ Y Q ρ
      orientation χ j (markedMemoryGhostChoiceTarget hZ s H.1) H.2.1
    have ht := ih (j+1) H.2.2
    exact congrArg₂ (fun a b : ℂ => a*b)
      (congrArg₂ (fun a b : ℂ => a*b) hg he) ht

theorem markedMemoryHistoryInclude_boundaryTerm (n : ℕ) (z₀ : Z)
    (s : MarkedRawState P (pads+1) B Z)
    (H : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryGeometricBoundaryHistoryTerm ν V hW ψ η d₀ Y Q ρ orientation qStage χ
        (⟨z₀.1, h z₀.2⟩ : W) (markedRawStateInclude h s)
        (markedMemoryHistoryInclude h hZ hW n H) =
      markedMemoryGeometricBoundaryHistoryTerm ν V hZ ψ η d₀ Y Q ρ orientation qStage
        (fun k s => χ k (markedRawStateInclude h s)) z₀ s H := by
  unfold markedMemoryGeometricBoundaryHistoryTerm
  rw [markedRawStateInclude_mass, markedRawStateInclude_boundary,
    markedMemoryHistoryInclude_geometricWeight, markedMemoryHistoryInclude_target,
    markedRawStateInclude_boundary]

end
end ArtinMatthews
