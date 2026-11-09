module

public import ArtinMatthews.MarkedMinorArcRawEdgeEnergyReduction
public import ArtinMatthews.MarkedMinorArcRawEdgeChargedPositive


set_option backward.privateInPublic true
@[expose] public section

/-! Exact column evaluation for the full literal edge Cauchy energy.
The column is the concrete reversed row with exchanged storage/promotion
charges, derived on the actual factorial symmetric memory space. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

theorem markedRawEdgeChoiceReverseEnergy_sum_eq_swapped_row
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (hV : ∀ j, 0 < V j)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) {v₀ : ℝ} (hv₀ : 0 < v₀)
    (χ f : MarkedRawState P (pads+1) B Z → ℂ)
    (hχ : ∀ z active, MarkedRawMemorySymmetric (fun m => χ (z,(active,m))))
    (hf : ∀ z active, MarkedRawMemorySymmetric (fun m => f (z,(active,m)))) :
    (∑ s, markedRawStateMass ν s *
      markedRawEdgeChoiceReverseEnergy ν V hZ ψ η d₀ Y Q ρ v₀ χ f s) =
      ∑ s, markedRawStateMass ν s * ‖f s‖ ^ 2 *
        markedRawEdgeChargedWeightedAbsRow ν (fun _ => 1) (fun j => ((V j)⁻¹ : ℝ)) hZ
          (fun target source => markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ source target)
          v₀ s (fun _ => 1) := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  apply Complex.ofReal_injective
  rw [markedRawEdgeChoiceReverseEnergy_sum_eq_reversed_action ν V hZ ψ η d₀ Y Q ρ v₀ χ f hχ hf]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro s _
  have hrow := markedRawEdgeChargedWeightedAbsRow_mul_weight_eq_apply ν
    (fun _ => 1) (fun j => (V j)⁻¹) hν (fun _ => zero_le_one)
    (fun j => (inv_pos.mpr (hV j)).le) hZ
    (fun target source => markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ source target) hv₀ s
  simp only [Complex.ofReal_one] at hrow
  rw [← hrow]
  have hw : (markedRawMemorySchurWeight v₀ s.2.2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (markedRawMemorySchurWeight_pos hv₀ s.2.2).ne'
  rw [Complex.ofReal_div]
  field_simp [hw]

end
end ArtinMatthews
