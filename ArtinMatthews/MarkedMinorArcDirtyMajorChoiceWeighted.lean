module

public import ArtinMatthews.MarkedMinorArcDirtyMajorChoiceRow
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeWeight


set_option backward.privateInPublic true
@[expose] public section

/-! True v0 memory-Schur weights and the actual source-slot average of
major comparison rows. The only weight loss is the fixed v0^K. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

def markedDirtyMajorChoiceWeightedRow {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (η ψ : ℝ → ℂ) (r d₀ Y Q ρ v₀ : ℝ) (w : Z → ℤ × ℤ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) (I : Finset J) : ℝ := by
  classical
  exact ∑ choice : MarkedDirtyFixedEdgeChoice hZ s I,
    markedRawEdgeChoicePrimeMass ν V hZ s choice.1 *
      ‖markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ
        (markedRawFirstGoodCutoff r d₀ Y w χ) (markedRawEdgeMajorDetector ψ Q Y) s choice.1‖ *
      (markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ s choice.1)/markedRawMemorySchurWeight v₀ s.2.2)

def markedDirtyMajorSymWeightedRow {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (η ψ : ℝ → ℂ) (r d₀ Y Q ρ v₀ : ℝ) (w : Z → ℤ × ℤ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) (I : Finset J) : ℝ :=
  ∑ σ : J → Equiv.Perm (Fin (pads+1)), markedDirtySourceSlotWeight pads σ *
    markedDirtyMajorChoiceWeightedRow ν V hZ η ψ r d₀ Y Q ρ v₀ w χ (markedRawSlotEquiv σ s) I

theorem markedDirtyMajorChoiceWeightedRow_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (hV : ∀ j, 0 < V j)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (η ψ : ℝ → ℂ) (r d₀ Y Q ρ v₀ : ℝ) (hv₀ : 1 ≤ v₀) (w : Z → ℤ × ℤ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) (I : Finset J) :
    markedDirtyMajorChoiceWeightedRow ν V hZ η ψ r d₀ Y Q ρ v₀ w χ s I ≤
      v₀^(Fintype.card J)*markedDirtyMajorChoiceRow ν V hZ η ψ r d₀ Y Q ρ w χ s I := by
  classical
  unfold markedDirtyMajorChoiceWeightedRow markedDirtyMajorChoiceRow
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro choice _
  exact (mul_le_mul_of_nonneg_left (markedDirtyRawEdge_target_weight_ratio_le hZ s choice.1 hv₀)
    (mul_nonneg (markedDirtyRawEdge_prime_mass_nonneg ν V hν hV hZ s choice.1) (norm_nonneg _))).trans_eq
      (by ring)

theorem markedDirtySourceSlotWeight_total {J : Type*} [Fintype J] [DecidableEq J] (pads : ℕ) :
    (∑ σ : J → Equiv.Perm (Fin (pads+1)), markedDirtySourceSlotWeight pads σ)=1 := by
  have hh := markedDirtySourceOmission_expectation pads (Fin.last pads) (fun _ : J → Fin (pads+1) => (1:ℝ))
  simp only [mul_one] at hh
  exact hh.trans (markedUniformOmissionWeight_total (Nat.succ_pos pads))

end ArtinMatthews
