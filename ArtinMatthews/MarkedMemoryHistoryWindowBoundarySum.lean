module

public import ArtinMatthews.MarkedMemoryHistoryWindowSum
public import ArtinMatthews.MarkedMemoryHistoryIncludeWeights


set_option backward.privateInPublic true
@[expose] public section

/-! The actual signed birth-distinct boundary term under the constructed
finite window-history reindexing. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z W : Finset (ℤ × ℤ)} (h : Z ⊆ W)
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (hW : ∀ z ∈ W, IsCoprime z.1 z.2)

theorem markedMemoryBirthDistinct_boundary_window_sum [DecidableEq J]
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B W → ℂ) (n : ℕ) (z₀ : Z) :
    markedMemoryBirthDistinctGeometricBoundaryPairing (N := n) ν V hZ ψ η d₀ Y Q ρ
      orientation qStage (fun j s => χ j (markedRawStateInclude h s)) z₀ =
      ∑ s : MarkedRawState P (pads+1) B W,
        ∑ H : MarkedMemoryChronologicalHistory hW n s,
          if MarkedMemoryHistoryVerticesIn hW Z H then
            if MarkedMemoryHistoryBirthDistinct hW H then
              markedMemoryGeometricBoundaryHistoryTerm ν V hW ψ η d₀ Y Q ρ
                orientation qStage χ (⟨z₀.1, h z₀.2⟩ : W) s H
            else 0
          else 0 := by
  classical
  have hs := markedMemoryHistoryWindow_sum h hZ hW n
    (fun s H => if MarkedMemoryHistoryBirthDistinct hW H then
      markedMemoryGeometricBoundaryHistoryTerm ν V hW ψ η d₀ Y Q ρ
        orientation qStage χ (⟨z₀.1, h z₀.2⟩ : W) s H else 0)
  simpa only [markedMemoryBirthDistinctGeometricBoundaryPairing,
    markedMemoryHistoryInclude_birthDistinct_iff, markedMemoryHistoryInclude_boundaryTerm] using hs


end
end ArtinMatthews
