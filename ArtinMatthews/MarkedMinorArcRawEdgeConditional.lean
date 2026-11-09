module

public import ArtinMatthews.MarkedMinorArcRawEdgeCrudeWeighted


set_option backward.privateInPublic true
@[expose] public section

/-! Conditional prime-tuple integration in the literal full edge row.
The gate is constant only on the genuine fixed-label target fibre. It
may couple different fresh groups through earlier-coordinate tests. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedRawEdgeConditionalAbsRow {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z)
    (gate : MarkedRawEdgeChoice hZ s → Prop) : ℝ :=
  ∑ choice : MarkedRawEdgeChoice hZ s, if gate choice then
    markedRawEdgeChoicePrimeMass ν V hZ s choice*‖markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s choice‖
  else 0

set_option backward.isDefEq.respectTransparency false in
theorem markedRawEdge_conditional_row_le
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p,0 ≤ ν j p) (hV : ∀ j,0 < V j) {C N D : ℝ}
    (hC : 1 ≤ C) (hVC : ∀ j,(V j)⁻¹ ≤ C) (hN : 0 ≤ N) (hD : 0 ≤ D)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (r d₀ Y Q ρ H W A : ℝ)
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
    markedRawEdgeConditionalAbsRow ν V hZ ψ η d₀ Y Q ρ χ s gate ≤
      D*(4*C*N)^(Fintype.card J)*(B+1:ℝ)^(Fintype.card J)*H^2*
        (33*W*(1+(2*A*Y+1)*(4*Q^3/Y))) := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  let E := H^2*(33*W*(1+(2*A*Y+1)*(4*Q^3/Y)))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hC₀ : 0 ≤ C := zero_le_one.trans hC
  have hfixed (I : Finset J) :
      (∑ choice : MarkedDirtyFixedEdgeChoice hZ s I, if gate choice.1 then
        markedRawEdgeChoicePrimeMass ν V hZ s choice.1*
          ‖markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s choice.1‖ else 0) ≤
      D*(2*C*N)^(Fintype.card J)*(B+1:ℝ)^(Fintype.card J)*E := by
    let μ := finiteProductMass (fun j : ↥(Finset.univ \ I) => ν j.1)
    have hμ (fresh) : 0 ≤ μ fresh := Finset.prod_nonneg (fun j _ => hν _ _)
    have hVP : 0 ≤ ∏ j ∈ I,(V j)⁻¹ := Finset.prod_nonneg (fun j _ => (inv_pos.mpr (hV j)).le)
    have hVB : (∏ j ∈ I,(V j)⁻¹) ≤ C^(Fintype.card J) := by
      calc
        _ ≤ ∏ _j ∈ I,C := Finset.prod_le_prod₀ (fun j _ => (inv_pos.mpr (hV j)).le) (fun j _ => hVC j)
        _ = C^I.card := by simp
        _ ≤ _ := pow_le_pow_right₀ hC (Finset.card_le_card (Finset.subset_univ I))
    have hpoint (store : J → Bool) (indices : MarkedRawPromotionTuple s.2.2 I)
        (fresh : (j : ↥(Finset.univ \ I)) → ↥(P j.1)) :
        (∑ choice ∈ markedDirtyMajorChoiceFiber hZ s I store indices fresh,
          if gate choice.1 then markedRawEdgeChoicePrimeMass ν V hZ s choice.1*
            ‖markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s choice.1‖ else 0) ≤
        C^(Fintype.card J)*E*(if freshGate I store indices fresh then μ fresh else 0) := by
      by_cases hg : freshGate I store indices fresh
      · have heq : (∑ choice ∈ markedDirtyMajorChoiceFiber hZ s I store indices fresh,
            if gate choice.1 then markedRawEdgeChoicePrimeMass ν V hZ s choice.1*
              ‖markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s choice.1‖ else 0) =
            (μ fresh*(∏ j ∈ I,(V j)⁻¹))*∑ choice ∈ markedDirtyMajorChoiceFiber hZ s I store indices fresh,
              ‖markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s choice.1‖ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro choice hc
          rw [ite_eq_left ((hgate I store indices fresh choice hc).mpr hg),
            markedDirtyMajorChoiceFiber_prime_mass ν V hZ s I store indices fresh choice hc]
        rw [heq,ite_eq_left hg]
        have hf := markedRawEdgeCrude_fiber_sum_le hZ ψ η r d₀ Y Q ρ H W A hY hQ hA hρ₀ hρ₁ hH hW
          hη hψ hsupp χ hχ s w hw hτ hbox I store indices fresh
        calc
          _ ≤ (μ fresh*C^(Fintype.card J))*E := mul_le_mul
            (mul_le_mul_of_nonneg_left hVB (hμ fresh)) hf
            (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (mul_nonneg (hμ fresh) (pow_nonneg hC₀ _))
          _ = _ := by ring
      · rw [ite_eq_right hg,mul_zero]
        apply le_of_eq
        apply Finset.sum_eq_zero
        intro choice hc
        exact ite_eq_right (fun hh => hg ((hgate I store indices fresh choice hc).mp hh))
    have hidx : (Fintype.card (MarkedRawPromotionTuple s.2.2 I):ℝ) ≤ (B+1:ℝ)^(Fintype.card J) := by
      have hh : Fintype.card (MarkedRawPromotionTuple s.2.2 I) ≤ (B+1)^(Fintype.card J) :=
        (markedRawPromotionTuple_card_le s.2.2 I).trans ((Nat.pow_le_pow_left (by omega : B ≤ B+1) _).trans
          (Nat.pow_le_pow_right (by omega : 1 ≤ B+1) (Finset.card_le_card (Finset.subset_univ I))))
      exact_mod_cast hh
    rw [markedDirtyMajorChoice_fiberwise_sum hZ s I]
    calc
      _ ≤ ∑ store : J → Bool,∑ indices : MarkedRawPromotionTuple s.2.2 I,
          C^(Fintype.card J)*E*(∑ fresh : (j : ↥(Finset.univ \ I)) → ↥(P j.1),
            if freshGate I store indices fresh then μ fresh else 0) := by
        apply Finset.sum_le_sum
        intro store _
        apply Finset.sum_le_sum
        intro indices _
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun fresh _ => hpoint store indices fresh)
      _ ≤ ∑ _store : J → Bool,∑ _indices : MarkedRawPromotionTuple s.2.2 I,
          C^(Fintype.card J)*E*(D*N^(Fintype.card J)) := by
        exact Finset.sum_le_sum (fun store _ => Finset.sum_le_sum (fun indices _ =>
          mul_le_mul_of_nonneg_left (hmass I store indices) (mul_nonneg (pow_nonneg hC₀ _) hE)))
      _ = (2:ℝ)^(Fintype.card J)*(Fintype.card (MarkedRawPromotionTuple s.2.2 I):ℝ)*
          (C^(Fintype.card J)*E*(D*N^(Fintype.card J))) := by simp [mul_assoc]
      _ ≤ (2:ℝ)^(Fintype.card J)*(B+1:ℝ)^(Fintype.card J)*
          (C^(Fintype.card J)*E*(D*N^(Fintype.card J))) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hidx (by positivity)) (by positivity)
      _ = _ := by simp only [mul_pow]; ring
  have heq : markedRawEdgeConditionalAbsRow ν V hZ ψ η d₀ Y Q ρ χ s gate =
      ∑ I : Finset J, ∑ choice : MarkedDirtyFixedEdgeChoice hZ s I,
        if gate choice.1 then markedRawEdgeChoicePrimeMass ν V hZ s choice.1*
          ‖markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s choice.1‖ else 0 := by
    have hh := Equiv.sum_comp (Equiv.sigmaFiberEquiv (fun c : MarkedRawEdgeChoice hZ s =>
      markedDirtyEdgePromotedGroups c.promotions))
      (fun c => if gate c then markedRawEdgeChoicePrimeMass ν V hZ s c*
        ‖markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s c‖ else 0)
    simpa only [Fintype.sum_sigma,Equiv.sigmaFiberEquiv_apply,markedRawEdgeConditionalAbsRow] using hh.symm
  rw [heq]
  calc
    _ ≤ ∑ _I : Finset J,D*(2*C*N)^(Fintype.card J)*(B+1:ℝ)^(Fintype.card J)*E :=
      Finset.sum_le_sum (fun I _ => hfixed I)
    _ = _ := by
      simp only [Finset.sum_const,Fintype.card_finset,Finset.card_univ,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
      dsimp [E]
      simp only [mul_pow]
      rw [show (4:ℝ)^(Fintype.card J)=(2:ℝ)^(Fintype.card J)*(2:ℝ)^(Fintype.card J) by
        rw [← mul_pow]; norm_num]
      ring

end ArtinMatthews
