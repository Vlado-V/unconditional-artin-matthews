module

public import ArtinMatthews.MarkedMemoryHistoryWindowBoundarySum
public import ArtinMatthews.MarkedMemoryHistoryWindowSupport


set_option backward.privateInPublic true
@[expose] public section

/-! Exact restriction of the original birth-distinct signed boundary
functional to a position window supporting its actual endpoint cutoffs.
The source prime measure, rho, both slot averages and memory cap are
unchanged. No extra bounded history test is inserted. -/

namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z W : Finset (ℤ × ℤ)} (h : Z ⊆ W)
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (hW : ∀ z ∈ W, IsCoprime z.1 z.2)
  (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
  (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
  (χ : ℕ → MarkedRawState P (pads+1) B W → ℂ)

theorem markedMemoryBirthDistinct_boundary_restrict
    (hχ : ∀ j s, s.1.1 ∉ Z → χ j s = 0) (n : ℕ) (z₀ : Z) :
    markedMemoryBirthDistinctGeometricBoundaryPairing (B := B) (N := n)
        ν V hW ψ η d₀ Y Q ρ orientation qStage χ (⟨z₀.1, h z₀.2⟩ : W) =
      markedMemoryBirthDistinctGeometricBoundaryPairing (B := B) (N := n)
        ν V hZ ψ η d₀ Y Q ρ orientation qStage
        (fun j s => χ j (markedRawStateInclude h s)) z₀ := by
  classical
  rw [markedMemoryBirthDistinct_boundary_window_sum h hZ hW ν V ψ η d₀ Y Q ρ
    orientation qStage χ n z₀]
  unfold markedMemoryBirthDistinctGeometricBoundaryPairing
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro H _
  by_cases hv : MarkedMemoryHistoryVerticesIn hW Z H
  · rw [ite_eq_left hv]
  · rw [ite_eq_right hv]
    by_cases hd : MarkedMemoryHistoryBirthDistinct hW H
    · rw [ite_eq_left hd]
      exact markedMemoryGeometricBoundaryTerm_zero_of_not_vertices hW ν V ψ η
        d₀ Y Q ρ orientation qStage χ hχ n (⟨z₀.1, h z₀.2⟩ : W) z₀.2 s H hv
    · exact ite_eq_right hd

theorem markedMemoryBirthDistinct_boundary_zero_of_cutoffs_zero
    (hχ : ∀ j s, χ j s = 0) (n : ℕ) (hn : 0 < n) (z₀ : W) :
    markedMemoryBirthDistinctGeometricBoundaryPairing (B := B) (N := n)
      ν V hW ψ η d₀ Y Q ρ orientation qStage χ z₀ = 0 := by
  classical
  unfold markedMemoryBirthDistinctGeometricBoundaryPairing
  apply Finset.sum_eq_zero
  intro s _
  apply Finset.sum_eq_zero
  intro H _
  by_cases hd : MarkedMemoryHistoryBirthDistinct hW H
  · rw [ite_eq_left hd]
    have hz := markedMemoryGeometricHistoryWeight_zero_of_cutoffs_zero hW ν V ψ η
      d₀ Y Q ρ orientation qStage χ hχ n 0 hn H
    simp only [markedMemoryGeometricBoundaryHistoryTerm, hz, mul_zero, zero_mul]
  · exact ite_eq_right hd

end
end ArtinMatthews
