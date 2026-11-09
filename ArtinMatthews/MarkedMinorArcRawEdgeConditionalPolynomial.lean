module

public import ArtinMatthews.MarkedMinorArcRawEdgeConditionalWeighted


set_option backward.privateInPublic true
@[expose] public section

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedRawEdge_conditional_weighted_row_le_polynomial
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p,0 ≤ ν j p) (hV : ∀ j,0 < V j) {C N D : ℝ}
    (hC : 1 ≤ C) (hVC : ∀ j,(V j)⁻¹ ≤ C) (hN : 0 ≤ N) (hD : 0 ≤ D)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (r d₀ Y Q ρ H W A v₀ : ℝ) (hv₀ : 1 ≤ v₀)
    (hY : 1 ≤ Y) (hQ : 1 ≤ Q) (hA : 0 ≤ A) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
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
        (33*W*(8*A+5))*Q^3 := by
  have hr := markedRawEdge_conditional_weighted_row_le ν V hν hV hC hVC hN hD
    hZ ψ η r d₀ Y Q ρ H W A v₀ hv₀ (zero_lt_one.trans_le hY) (zero_le_one.trans hQ)
    hA hρ₀ hρ₁ hH hW hη hψ hsupp χ hχ s w hw hτ hbox gate freshGate hgate hmass
  have hp : 0 ≤ D*v₀^(Fintype.card J)*(4*C*N)^(Fintype.card J)*(B+1:ℝ)^(Fintype.card J)*H^2 := by
    have hC₀ := zero_le_one.trans hC
    have hv₀₀ := zero_le_one.trans hv₀
    positivity
  exact hr.trans ((mul_le_mul_of_nonneg_left
    (markedRawEdgeCrude_kernel_factor_le_polynomial hY hQ hW) hp).trans_eq (by ring))

end ArtinMatthews
