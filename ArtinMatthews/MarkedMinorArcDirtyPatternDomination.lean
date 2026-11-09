module

public import ArtinMatthews.MarkedMinorArcRawEdgePatternPartition


set_option backward.privateInPublic true
@[expose] public section

/-! Pointwise coefficient domination passes to the literal patterned
weighted rows and their actual source-slot averages. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

theorem markedRawEdgePatternWeightedRow_mono
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (A D : MarkedRawEdgePatternKernel P pads B Z) {v₀ : ℝ} (hv₀ : 0 < v₀)
    (hAD : ∀ p q s t,‖A p q s t‖ ≤ ‖D p q s t‖) (s : MarkedRawState P (pads+1) B Z) :
    markedRawEdgePatternWeightedRow ν δ γ hZ A v₀ s ≤ markedRawEdgePatternWeightedRow ν δ γ hZ D v₀ s := by
  classical
  unfold markedRawEdgePatternWeightedRow
  apply Finset.sum_le_sum
  intro c _
  simp only [norm_mul]
  apply mul_le_mul_of_nonneg_right _
    (div_nonneg (markedRawMemorySchurWeight_pos hv₀ _).le (markedRawMemorySchurWeight_pos hv₀ _).le)
  exact mul_le_mul_of_nonneg_left (hAD _ _ _ _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem markedRawEdgePatternWeightedAverage_mono
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (A D : MarkedRawEdgePatternKernel P pads B Z) {v₀ : ℝ} (hv₀ : 0 < v₀)
    (hAD : ∀ p q s t,‖A p q s t‖ ≤ ‖D p q s t‖) (s : MarkedRawState P (pads+1) B Z) :
    markedRawSlotAverageReal (markedRawEdgePatternWeightedRow ν δ γ hZ A v₀) s ≤
      markedRawSlotAverageReal (markedRawEdgePatternWeightedRow ν δ γ hZ D v₀) s := by
  unfold markedRawSlotAverageReal
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact Finset.sum_le_sum (fun _ _ => markedRawEdgePatternWeightedRow_mono ν δ γ hZ A D hv₀ hAD _)

theorem markedRawEdgeFlagGate_weightedAverage_le
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (F : (J → Bool) → (J → Bool) → Prop) (A : MarkedRawEdgePatternKernel P pads B Z)
    {v₀ : ℝ} (hv₀ : 0 < v₀) (s : MarkedRawState P (pads+1) B Z) :
    markedRawSlotAverageReal (markedRawEdgePatternWeightedRow ν δ γ hZ (markedRawEdgeFlagGate F A) v₀) s ≤
      markedRawSlotAverageReal (markedRawEdgePatternWeightedRow ν δ γ hZ A v₀) s := by
  apply markedRawEdgePatternWeightedAverage_mono ν δ γ hZ _ A hv₀ _ s
  intro p q u v
  classical
  unfold markedRawEdgeFlagGate
  split_ifs
  · exact le_rfl
  · exact (norm_zero.trans_le (norm_nonneg _))

end
end ArtinMatthews
