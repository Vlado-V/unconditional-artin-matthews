module

public import ArtinMatthews.MarkedMinorArcDirtySignedRow


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite partition of the promoted sector. This includes every
store subset; pure stores remain a distinct sector rather than disappearing. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedDirty_promoted_choice_sum {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (f : MarkedRawEdgeChoice hZ s → ℝ) :
    (∑ c : MarkedRawEdgeChoice hZ s,if (markedDirtyEdgePromotedGroups c.promotions).Nonempty then f c else 0) =
      ∑ I : Finset J,if I.Nonempty then ∑ c : MarkedDirtyFixedEdgeChoice hZ s I,f c.1 else 0 := by
  classical
  have hh := Equiv.sum_comp (Equiv.sigmaFiberEquiv (fun c : MarkedRawEdgeChoice hZ s =>
    markedDirtyEdgePromotedGroups c.promotions))
    (fun c => if (markedDirtyEdgePromotedGroups c.promotions).Nonempty then f c else 0)
  rw [← hh]
  simp only [Fintype.sum_sigma,Equiv.sigmaFiberEquiv_apply]
  apply Finset.sum_congr rfl
  intro I _
  by_cases hI : I.Nonempty
  · rw [ite_eq_left hI]
    apply Finset.sum_congr rfl
    intro c _
    rw [c.2,ite_eq_left hI]
  · rw [ite_eq_right hI]
    apply Finset.sum_eq_zero
    intro c _
    rw [c.2,ite_eq_right hI]

def markedDirtyPromotedWeightedRow {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (r d₀ Y Q ρ v₀ : ℝ) (w : Z → ℤ × ℤ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z)
    (modifier : (σ : J → Equiv.Perm (Fin (pads+1))) → MarkedRawEdgeChoice hZ (markedRawSlotEquiv σ s) → ℂ) : ℝ :=
  ∑ σ : J → Equiv.Perm (Fin (pads+1)),markedDirtySourceSlotWeight pads σ*
    ∑ c : MarkedRawEdgeChoice hZ (markedRawSlotEquiv σ s),
      if (markedDirtyEdgePromotedGroups c.promotions).Nonempty then
        markedRawEdgeChoicePrimeMass ν V hZ (markedRawSlotEquiv σ s) c*
          ‖modifier σ c*markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ
            (markedRawFirstGoodCutoff r d₀ Y w χ) (markedRawSlotEquiv σ s) c‖*
          (markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ (markedRawSlotEquiv σ s) c)/
            markedRawMemorySchurWeight v₀ (markedRawSlotEquiv σ s).2.2)
      else 0

theorem markedDirtyPromotedWeightedRow_partition {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (r d₀ Y Q ρ v₀ : ℝ) (w : Z → ℤ × ℤ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z)
    (modifier : (σ : J → Equiv.Perm (Fin (pads+1))) → MarkedRawEdgeChoice hZ (markedRawSlotEquiv σ s) → ℂ) :
    markedDirtyPromotedWeightedRow ν V hZ ψ η r d₀ Y Q ρ v₀ w χ s modifier =
      ∑ I : Finset J,if I.Nonempty then
        markedDirtySignedFixedWeightedRow ν V hZ ψ η r d₀ Y Q ρ v₀ w χ s I modifier else 0 := by
  classical
  unfold markedDirtyPromotedWeightedRow
  simp_rw [markedDirty_promoted_choice_sum,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I _
  by_cases hI : I.Nonempty
  · simp only [ite_eq_left hI]
    rfl
  · simp only [ite_eq_right hI,mul_zero,Finset.sum_const_zero]

theorem markedDirtyPromotedWeightedRow_le_of_fixed {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (r d₀ Y Q ρ v₀ : ℝ) (w : Z → ℤ × ℤ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z)
    (modifier : (σ : J → Equiv.Perm (Fin (pads+1))) → MarkedRawEdgeChoice hZ (markedRawSlotEquiv σ s) → ℂ)
    {R : ℝ} (hR : 0 ≤ R)
    (hfixed : ∀ I : Finset J,I.Nonempty →
      markedDirtySignedFixedWeightedRow ν V hZ ψ η r d₀ Y Q ρ v₀ w χ s I modifier ≤ R) :
    markedDirtyPromotedWeightedRow ν V hZ ψ η r d₀ Y Q ρ v₀ w χ s modifier ≤ (2:ℝ)^(Fintype.card J)*R := by
  classical
  rw [markedDirtyPromotedWeightedRow_partition]
  calc
    _ ≤ ∑ _I : Finset J,R := by
      apply Finset.sum_le_sum
      intro I _
      split_ifs with hI
      · exact hfixed I hI
      · exact hR
    _ = _ := by simp

end
end ArtinMatthews
