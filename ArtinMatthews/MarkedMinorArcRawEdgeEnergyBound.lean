module

public import ArtinMatthews.MarkedMinorArcRawEdgeEnergyColumn


set_option backward.privateInPublic true
@[expose] public section

/-! Schur energy reduction for the original full physical edge, using
the proved actual factorial column identity.  The concrete arithmetic
row estimates can be substituted directly into its two explicit bounds. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

theorem markedRawEdgeApply_energy_le_of_rows
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (hV : ∀ j, 0 < V j)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) {v₀ R : ℝ} (hv₀ : 0 < v₀) (hR : 0 ≤ R)
    (χ f : MarkedRawState P (pads+1) B Z → ℂ)
    (hχ : ∀ z active, MarkedRawMemorySymmetric (fun m => χ (z,(active,m))))
    (hf : ∀ z active, MarkedRawMemorySymmetric (fun m => f (z,(active,m))))
    (hrow : ∀ s, markedRawEdgeCrudeWeightedAbsRow ν V hZ ψ η d₀ Y Q ρ v₀ χ s (fun _ => 1) ≤ R)
    (hcolumn : ∀ s, markedRawEdgeChargedWeightedAbsRow ν (fun _ => 1)
      (fun j => ((V j)⁻¹ : ℝ)) hZ
      (fun target source => markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ source target)
      v₀ s (fun _ => 1) ≤ R) :
    (∑ s, markedRawStateMass ν s * ‖markedRawEdgeApply ν V hZ ψ η d₀ Y Q ρ χ f s‖ ^ 2) ≤
      R ^ 2 * ∑ s, markedRawStateMass ν s * ‖f s‖ ^ 2 := by
  classical
  calc
    _ ≤ R * ∑ s, markedRawStateMass ν s *
        markedRawEdgeChoiceReverseEnergy ν V hZ ψ η d₀ Y Q ρ v₀ χ f s := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro s _
      have hc := markedRawEdgeApply_choice_cauchy ν V hν hV hZ ψ η d₀ Y Q ρ hv₀ χ f s
      have he := markedRawEdgeChoiceReverseEnergy_nonneg ν V hν hV hZ ψ η d₀ Y Q ρ hv₀ χ f s
      calc
        _ ≤ markedRawStateMass ν s *
            (markedRawEdgeCrudeWeightedAbsRow ν V hZ ψ η d₀ Y Q ρ v₀ χ s (fun _ => 1) *
              markedRawEdgeChoiceReverseEnergy ν V hZ ψ η d₀ Y Q ρ v₀ χ f s) :=
          mul_le_mul_of_nonneg_left hc (markedRawStateMass_nonneg ν hν s)
        _ ≤ markedRawStateMass ν s *
            (R * markedRawEdgeChoiceReverseEnergy ν V hZ ψ η d₀ Y Q ρ v₀ χ f s) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hrow s) he)
            (markedRawStateMass_nonneg ν hν s)
        _ = _ := by ring
    _ = R * ∑ s, markedRawStateMass ν s * ‖f s‖ ^ 2 *
        markedRawEdgeChargedWeightedAbsRow ν (fun _ => 1) (fun j => ((V j)⁻¹ : ℝ)) hZ
          (fun target source => markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ source target)
          v₀ s (fun _ => 1) := by
      rw [markedRawEdgeChoiceReverseEnergy_sum_eq_swapped_row ν V hν hV hZ ψ η d₀ Y Q ρ hv₀ χ f hχ hf]
    _ ≤ R * (R * ∑ s, markedRawStateMass ν s * ‖f s‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hR
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro s _
      calc
        _ ≤ markedRawStateMass ν s * ‖f s‖ ^ 2 * R :=
          mul_le_mul_of_nonneg_left (hcolumn s)
            (mul_nonneg (markedRawStateMass_nonneg ν hν s) (sq_nonneg _))
        _ = _ := by ring
    _ = _ := by ring

end
end ArtinMatthews
