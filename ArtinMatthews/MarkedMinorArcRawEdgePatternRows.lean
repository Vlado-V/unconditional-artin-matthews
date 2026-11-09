module

public import ArtinMatthews.MarkedMinorArcRawEdgeSectorTranspose
public import ArtinMatthews.MarkedMinorArcRawEdgeSlotTranspose
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeOmissionAverage


set_option backward.privateInPublic true
@[expose] public section

/-! The patterned weighted rows are exactly the literal detector-choice
sums used by the arithmetic row bounds, with every modifier retained. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

theorem markedRawEdgePatternWeightedRow_detector_original
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (hV : ∀ j, 0 < V j)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (η : ℝ → ℂ) (d₀ Y ρ v₀ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (D : ℤ → ℤ → ℤ → ℂ)
    (β : MarkedRawEdgePatternKernel P pads B Z) (s : MarkedRawState P (pads+1) B Z) :
    markedRawEdgePatternWeightedRow ν (fun j => ((V j)⁻¹ : ℝ)) (fun _ => 1) hZ
      (fun p q u v => β p q u v * markedRawEdgeJointDetectorCoefficient hZ η d₀ Y ρ χ D u v) v₀ s =
      ∑ c : MarkedRawEdgeChoice hZ s, markedRawEdgeChoicePrimeMass ν V hZ s c *
        ‖β (markedRawEdgeChoicePromoted c) c.store s (markedRawEdgeTargetState hZ s c) *
          markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ D s c‖ *
        (markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ s c) /
          markedRawMemorySchurWeight v₀ s.2.2) := by
  classical
  unfold markedRawEdgePatternWeightedRow
  apply Finset.sum_congr rfl
  intro c _
  rw [markedRawEdgeChoiceCharge_original, markedRawEdgeChoiceDetectorCoefficient_eq_joint]
  have hm := markedDirtyRawEdge_prime_mass_nonneg ν V hν hV hZ s c
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hm]

theorem markedRawEdgePatternWeightedRow_detector_average
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (hV : ∀ j, 0 < V j)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (η : ℝ → ℂ) (d₀ Y ρ v₀ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (D : ℤ → ℤ → ℤ → ℂ)
    (β : MarkedRawEdgePatternKernel P pads B Z) (s : MarkedRawState P (pads+1) B Z) :
    markedRawSlotAverageReal
      (markedRawEdgePatternWeightedRow ν (fun j => ((V j)⁻¹ : ℝ)) (fun _ => 1) hZ
        (fun p q u v => β p q u v * markedRawEdgeJointDetectorCoefficient hZ η d₀ Y ρ χ D u v) v₀) s =
      ∑ σ : (j : J) → Equiv.Perm (Fin (pads+1)), markedDirtySourceSlotWeight pads σ *
        ∑ c : MarkedRawEdgeChoice hZ (markedRawSlotEquiv σ s),
          markedRawEdgeChoicePrimeMass ν V hZ (markedRawSlotEquiv σ s) c *
          ‖β (markedRawEdgeChoicePromoted c) c.store (markedRawSlotEquiv σ s)
              (markedRawEdgeTargetState hZ (markedRawSlotEquiv σ s) c) *
            markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ D (markedRawSlotEquiv σ s) c‖ *
          (markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ (markedRawSlotEquiv σ s) c) /
            markedRawMemorySchurWeight v₀ (markedRawSlotEquiv σ s).2.2) := by
  classical
  unfold markedRawSlotAverageReal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [markedDirtySourceSlotWeight_eq, one_div,
    markedRawEdgePatternWeightedRow_detector_original ν V hν hV]

theorem markedRawEdgePatternWeightedRow_detector_reverse
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (η : ℝ → ℂ) (d₀ Y ρ v₀ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (D : ℤ → ℤ → ℤ → ℂ)
    (β : MarkedRawEdgePatternKernel P pads B Z) (s : MarkedRawState P (pads+1) B Z) :
    markedRawEdgePatternWeightedRow ν δ γ hZ
      (markedRawEdgePatternReverse
        (fun p q u v => β p q u v * markedRawEdgeJointDetectorCoefficient hZ η d₀ Y ρ χ D u v)) v₀ s =
      markedRawEdgePatternWeightedRow ν δ γ hZ
        (fun p q u v => markedRawEdgePatternReverse β p q u v *
          markedRawEdgeJointDetectorCoefficient hZ η d₀ Y ρ χ (markedRawEdgeReverseDetector D) u v) v₀ s := by
  unfold markedRawEdgePatternWeightedRow
  apply Finset.sum_congr rfl
  intro c _
  dsimp only [markedRawEdgePatternReverse]
  rw [markedRawEdgeJointDetector_target_reverse hdisj hZ η d₀ Y ρ χ D s c]

end
end ArtinMatthews
