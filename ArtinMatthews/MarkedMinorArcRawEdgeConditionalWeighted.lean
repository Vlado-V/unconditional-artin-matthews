module

public import ArtinMatthews.MarkedMinorArcRawEdgeConditional


set_option backward.privateInPublic true
@[expose] public section

/-! The conditional full-edge row with the literal pending-memory Schur
weight. All fresh-value constraints remain inside the actual choice sum. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedRawEdgeConditionalWeightedAbsRow {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ v₀ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z)
    (gate : MarkedRawEdgeChoice hZ s → Prop) : ℝ :=
  ∑ choice : MarkedRawEdgeChoice hZ s, if gate choice then
    markedRawEdgeChoicePrimeMass ν V hZ s choice*‖markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s choice‖*
      (markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ s choice)/
        markedRawMemorySchurWeight v₀ s.2.2)
  else 0

theorem markedRawEdge_conditional_weighted_le_unweighted
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p,0 ≤ ν j p) (hV : ∀ j,0 < V j)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ v₀ : ℝ) (hv₀ : 1 ≤ v₀)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z)
    (gate : MarkedRawEdgeChoice hZ s → Prop) :
    markedRawEdgeConditionalWeightedAbsRow ν V hZ ψ η d₀ Y Q ρ v₀ χ s gate ≤
      v₀^(Fintype.card J)*markedRawEdgeConditionalAbsRow ν V hZ ψ η d₀ Y Q ρ χ s gate := by
  unfold markedRawEdgeConditionalWeightedAbsRow markedRawEdgeConditionalAbsRow
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro choice _
  split_ifs
  · have hm := markedDirtyRawEdge_prime_mass_nonneg ν V hν hV hZ s choice
    exact (mul_le_mul_of_nonneg_left (markedDirtyRawEdge_target_weight_ratio_le hZ s choice hv₀)
      (mul_nonneg hm (norm_nonneg _))).trans_eq (by ring)
  · simp only [mul_zero,le_refl]

theorem markedRawEdge_conditional_weighted_row_le
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p,0 ≤ ν j p) (hV : ∀ j,0 < V j) {C N D : ℝ}
    (hC : 1 ≤ C) (hVC : ∀ j,(V j)⁻¹ ≤ C) (hN : 0 ≤ N) (hD : 0 ≤ D)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (r d₀ Y Q ρ H W A v₀ : ℝ) (hv₀ : 1 ≤ v₀)
    (hY : 0 < Y) (hQ : 0 ≤ Q) (hA : 0 ≤ A) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (hH : 0 ≤ H) (hW : 0 ≤ W) (hη : ∀ t,‖η t‖ ≤ H) (hψ : ∀ t,‖ψ t‖ ≤ W)
    (hsupp : ∀ t,ψ t ≠ 0 → |t| ≤ A)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (hχ : ∀ s,‖χ s‖ ≤ 1)
    (s : MarkedRawState P (pads+1) B Z) (w : ℤ × ℤ) (hw : markedMinorIntegerDet s.1.1 w=1)
    (hτ : markedMinorIntegerTau r s.1.1 ≠ 0)
    (hbox : ∀ v ∈ Z,|markedMinorIntegerTau r v/markedMinorIntegerTau r s.1.1| ≤ 16)
    (gate : MarkedRawEdgeChoice hZ s → Prop)
    (freshGate : (I : Finset J) → (J → Bool) → MarkedRawPromotionTuple s.2.2 I →
      ((j : ↥(Finset.univ \ I)) → ↥(P j.1)) → Prop)
    (hgate : ∀ I store indices fresh (c : MarkedDirtyFixedEdgeChoice hZ s I),
      c ∈ markedDirtyMajorChoiceFiber hZ s I store indices fresh →
        (gate c.1 ↔ freshGate I store indices fresh))
    (hmass : ∀ I store indices,
      (∑ fresh : (j : ↥(Finset.univ \ I)) → ↥(P j.1),
        if freshGate I store indices fresh then
          finiteProductMass (fun j : ↥(Finset.univ \ I) => ν j.1) fresh else 0) ≤
      D*N^(Fintype.card J)) :
    markedRawEdgeConditionalWeightedAbsRow ν V hZ ψ η d₀ Y Q ρ v₀ χ s gate ≤
      D*v₀^(Fintype.card J)*(4*C*N)^(Fintype.card J)*(B+1:ℝ)^(Fintype.card J)*H^2*
        (33*W*(1+(2*A*Y+1)*(4*Q^3/Y))) := by
  have hrow := markedRawEdge_conditional_row_le ν V hν hV hC hVC hN hD
    hZ ψ η r d₀ Y Q ρ H W A hY hQ hA hρ₀ hρ₁ hH hW hη hψ hsupp
    χ hχ s w hw hτ hbox gate freshGate hgate hmass
  exact (markedRawEdge_conditional_weighted_le_unweighted ν V hν hV hZ ψ η d₀ Y Q ρ v₀ hv₀
    χ s gate).trans ((mul_le_mul_of_nonneg_left hrow
      (pow_nonneg (zero_le_one.trans hv₀) _)).trans_eq (by ring))

end ArtinMatthews
