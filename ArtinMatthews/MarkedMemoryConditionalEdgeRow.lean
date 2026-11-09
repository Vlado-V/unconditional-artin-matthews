module

public import ArtinMatthews.MarkedMemoryHistoryEdgeChoice
public import ArtinMatthews.MarkedMinorArcRawEdgeConditionalWeighted
public import ArtinMatthews.MarkedMinorArcDirtyMajorChoiceWeighted


set_option backward.privateInPublic true
@[expose] public section

/-! Exact conditional rows for both literal slot averages. The two
uniform permutation weights cancel their actual finite cardinalities. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedMemoryEdgeChoiceWeight_norm
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p,0 ≤ ν j p) (hV : ∀ j,0 < V j)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z)
    (c : MarkedMemoryEdgeChoice hZ s) :
    ‖markedMemoryEdgeChoiceWeight ν V hZ ψ η d₀ Y Q ρ χ s c‖=
      markedDirtySourceSlotWeight pads c.1*
        markedRawEdgeChoicePrimeMass ν V hZ (markedRawSlotEquiv c.1 s) c.2.1*
        ‖markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ (markedRawSlotEquiv c.1 s) c.2.1‖*
          markedDirtySourceSlotWeight pads c.2.2 := by
  unfold markedMemoryEdgeChoiceWeight
  simp only [norm_mul,norm_inv,Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (markedDirtyRawEdge_prime_mass_nonneg ν V hν hV hZ (markedRawSlotEquiv c.1 s) c.2.1)]
  rw [markedDirtySourceSlotWeight_eq,markedDirtySourceSlotWeight_eq]
  simp only [one_div]

def markedMemoryConditionalEdgeRow
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ v₀ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (gate : (s : MarkedRawState P (pads+1) B Z) → MarkedRawEdgeChoice hZ s → Prop)
    (s : MarkedRawState P (pads+1) B Z) : ℝ :=
  ∑ c : MarkedMemoryEdgeChoice hZ s, if gate (markedRawSlotEquiv c.1 s) c.2.1 then
    ‖markedMemoryEdgeChoiceWeight ν V hZ ψ η d₀ Y Q ρ χ s c‖*
      (markedRawMemorySchurWeight v₀ (markedMemoryEdgeChoiceTarget hZ s c).2.2/
        markedRawMemorySchurWeight v₀ s.2.2)
  else 0

set_option backward.isDefEq.respectTransparency false in
theorem markedMemoryConditionalEdgeRow_eq
    {J : Type*} [Fintype J] [decJ : DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p,0 ≤ ν j p) (hV : ∀ j,0 < V j)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ v₀ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (gate : (s : MarkedRawState P (pads+1) B Z) → MarkedRawEdgeChoice hZ s → Prop)
    (s : MarkedRawState P (pads+1) B Z) :
    markedMemoryConditionalEdgeRow ν V hZ ψ η d₀ Y Q ρ v₀ χ gate s =
      ∑ σ : MarkedMemorySlotPermutations J (pads+1),markedDirtySourceSlotWeight pads σ*
        markedRawEdgeConditionalWeightedAbsRow ν V hZ ψ η d₀ Y Q ρ v₀ χ
          (markedRawSlotEquiv σ s) (gate (markedRawSlotEquiv σ s)) := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  unfold markedMemoryConditionalEdgeRow
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Fintype.sum_prod_type]
  have hinner (edge : MarkedRawEdgeChoice hZ (markedRawSlotEquiv σ s)) :
      (∑ τ : MarkedMemorySlotPermutations J (pads+1),
        if gate (markedRawSlotEquiv σ s) edge then
          ‖markedMemoryEdgeChoiceWeight ν V hZ ψ η d₀ Y Q ρ χ s ⟨σ,edge,τ⟩‖*
            (markedRawMemorySchurWeight v₀ (markedMemoryEdgeChoiceTarget hZ s ⟨σ,edge,τ⟩).2.2/
              markedRawMemorySchurWeight v₀ s.2.2) else 0) =
      markedDirtySourceSlotWeight pads σ*
        (if gate (markedRawSlotEquiv σ s) edge then
          markedRawEdgeChoicePrimeMass ν V hZ (markedRawSlotEquiv σ s) edge*
            ‖markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ (markedRawSlotEquiv σ s) edge‖*
              (markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ (markedRawSlotEquiv σ s) edge)/
                markedRawMemorySchurWeight v₀ (markedRawSlotEquiv σ s).2.2) else 0) := by
    by_cases hg : gate (markedRawSlotEquiv σ s) edge
    · simp only [ite_eq_left hg,markedMemoryEdgeChoiceWeight_norm ν V hν hV]
      change (∑ τ : MarkedMemorySlotPermutations J (pads+1),
        (markedDirtySourceSlotWeight pads σ*markedRawEdgeChoicePrimeMass ν V hZ (markedRawSlotEquiv σ s) edge*
          ‖markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ (markedRawSlotEquiv σ s) edge‖*
            markedDirtySourceSlotWeight pads τ)*
          (markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ (markedRawSlotEquiv σ s) edge)/
            markedRawMemorySchurWeight v₀ (markedRawSlotEquiv σ s).2.2)) = _
      simp_rw [mul_right_comm _ (markedDirtySourceSlotWeight pads _)]
      rw [← Finset.mul_sum,markedDirtySourceSlotWeight_total,mul_one]
      ring
    · simp only [ite_eq_right hg,Finset.sum_const_zero,mul_zero]
  simp_rw [hinner]
  rw [← Finset.mul_sum]
  rfl

theorem markedMemoryConditionalEdgeRow_le
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p,0 ≤ ν j p) (hV : ∀ j,0 < V j)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ v₀ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (gate : (s : MarkedRawState P (pads+1) B Z) → MarkedRawEdgeChoice hZ s → Prop)
    (s : MarkedRawState P (pads+1) B Z) {R : ℝ}
    (hrow : ∀ σ : MarkedMemorySlotPermutations J (pads+1),
      markedRawEdgeConditionalWeightedAbsRow ν V hZ ψ η d₀ Y Q ρ v₀ χ
        (markedRawSlotEquiv σ s) (gate (markedRawSlotEquiv σ s)) ≤ R) :
    markedMemoryConditionalEdgeRow ν V hZ ψ η d₀ Y Q ρ v₀ χ gate s ≤ R := by
  rw [markedMemoryConditionalEdgeRow_eq ν V hν hV]
  calc
    _ ≤ ∑ σ : MarkedMemorySlotPermutations J (pads+1),markedDirtySourceSlotWeight pads σ*R :=
      Finset.sum_le_sum (fun σ _ => mul_le_mul_of_nonneg_left (hrow σ)
        (by unfold markedDirtySourceSlotWeight; positivity))
    _ = _ := by rw [← Finset.sum_mul,markedDirtySourceSlotWeight_total,one_mul]

end ArtinMatthews
