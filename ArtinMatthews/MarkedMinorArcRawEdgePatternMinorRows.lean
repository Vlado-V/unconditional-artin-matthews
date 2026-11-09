module

public import ArtinMatthews.MarkedMinorArcRawEdgePatternRows
public import ArtinMatthews.MarkedMinorArcRawEdgeChargedReverse
public import ArtinMatthews.MarkedMinorArcRawEdgeChargeSwap


set_option backward.privateInPublic true
@[expose] public section

/-! The full minor detector in patterned rows, including the exact
swapped charge and reflected physical kernel. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

def markedRawEdgeFlagChargeSwap {J : Type*} [Fintype J]
    (V : J → ℝ) (p q : J → Bool) : ℂ :=
  ∏ j, (if p j then (V j : ℂ) else 1) * (if q j then (((V j)⁻¹ : ℝ) : ℂ) else 1)

theorem markedRawEdgeFlagChargeSwap_choice {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (c : MarkedRawEdgeChoice hZ s) :
    markedRawEdgeFlagChargeSwap V (markedRawEdgeChoicePromoted c) c.store =
      markedRawEdgeChargeSwapModifier V hZ s c := rfl

theorem markedRawEdgePatternWeightedRow_swap {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hV : ∀ j,V j ≠ 0) {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (A : MarkedRawEdgePatternKernel P pads B Z)
    (v₀ : ℝ) (s : MarkedRawState P (pads+1) B Z) :
    markedRawEdgePatternWeightedRow ν (fun _ => 1) (fun j => ((V j)⁻¹ : ℝ)) hZ A v₀ s =
      markedRawEdgePatternWeightedRow ν (fun j => ((V j)⁻¹ : ℝ)) (fun _ => 1) hZ
        (fun p q u v => markedRawEdgeFlagChargeSwap V p q * A p q u v) v₀ s := by
  unfold markedRawEdgePatternWeightedRow
  apply Finset.sum_congr rfl
  intro c _
  rw [markedRawEdgeChoiceCharge_swap ν V hV,markedRawEdgeChoiceCharge_original]
  dsimp only
  rw [markedRawEdgeFlagChargeSwap_choice]
  rw [mul_assoc]

theorem markedRawEdgePatternWeightedRow_minor_original
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (hV : ∀ j, 0 < V j)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ v₀ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (β : MarkedRawEdgePatternKernel P pads B Z) (s : MarkedRawState P (pads+1) B Z) :
    markedRawEdgePatternWeightedRow ν (fun j => ((V j)⁻¹ : ℝ)) (fun _ => 1) hZ
      (fun p q u v => β p q u v * markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ u v) v₀ s =
      ∑ c : MarkedRawEdgeChoice hZ s, markedRawEdgeChoicePrimeMass ν V hZ s c *
        ‖β (markedRawEdgeChoicePromoted c) c.store s (markedRawEdgeTargetState hZ s c) *
          markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s c‖ *
        (markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ s c) /
          markedRawMemorySchurWeight v₀ s.2.2) := by
  unfold markedRawEdgePatternWeightedRow
  apply Finset.sum_congr rfl
  intro c _
  rw [markedRawEdgeChoiceCharge_original,markedRawEdgeChoiceCoefficient_eq_joint]
  have hm := markedDirtyRawEdge_prime_mass_nonneg ν V hν hV hZ s c
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hm]

theorem markedRawEdgePatternWeightedRow_minor_average
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (hV : ∀ j, 0 < V j)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ v₀ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (β : MarkedRawEdgePatternKernel P pads B Z) (s : MarkedRawState P (pads+1) B Z) :
    markedRawSlotAverageReal
      (markedRawEdgePatternWeightedRow ν (fun j => ((V j)⁻¹ : ℝ)) (fun _ => 1) hZ
        (fun p q u v => β p q u v * markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ u v) v₀) s =
      ∑ σ : (j : J) → Equiv.Perm (Fin (pads+1)),markedDirtySourceSlotWeight pads σ *
        ∑ c : MarkedRawEdgeChoice hZ (markedRawSlotEquiv σ s),
          markedRawEdgeChoicePrimeMass ν V hZ (markedRawSlotEquiv σ s) c *
          ‖β (markedRawEdgeChoicePromoted c) c.store (markedRawSlotEquiv σ s)
              (markedRawEdgeTargetState hZ (markedRawSlotEquiv σ s) c) *
            markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ (markedRawSlotEquiv σ s) c‖ *
          (markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ (markedRawSlotEquiv σ s) c) /
            markedRawMemorySchurWeight v₀ (markedRawSlotEquiv σ s).2.2) := by
  unfold markedRawSlotAverageReal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [markedDirtySourceSlotWeight_eq,one_div,
    markedRawEdgePatternWeightedRow_minor_original ν V hν hV]

theorem markedRawEdgePatternWeightedRow_minor_reverse
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ v₀ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (β : MarkedRawEdgePatternKernel P pads B Z) (s : MarkedRawState P (pads+1) B Z) :
    markedRawEdgePatternWeightedRow ν δ γ hZ
      (markedRawEdgePatternReverse
        (fun p q u v => β p q u v * markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ u v)) v₀ s =
      markedRawEdgePatternWeightedRow ν δ γ hZ
        (fun p q u v => markedRawEdgePatternReverse β p q u v *
          markedRawEdgeJointCoefficient hZ (markedRawEdgeReflectedCutoff ψ) η d₀ Y Q ρ χ u v) v₀ s := by
  unfold markedRawEdgePatternWeightedRow
  apply Finset.sum_congr rfl
  intro c _
  dsimp only [markedRawEdgePatternReverse]
  simp only [norm_mul]
  rw [markedRawEdgeJointCoefficient_target_norm_reverse hdisj hZ ψ η d₀ Y Q ρ χ s c]

end
end ArtinMatthews
