module

public import ArtinMatthews.MarkedMinorArcRawEdgeCrudeRow
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeWeight


set_option backward.privateInPublic true
@[expose] public section

/-! The literal full signed edge row with its true total-degree Schur
weight. A bounded factor may depend on the entire indexed edge choice. -/
noncomputable section
namespace ArtinMatthews
open scoped BigOperators

/-- Reversing the true memory weight costs at most one v₀ for each group:
an edge removes at most one indexed old particle in each group. -/
theorem markedRawEdgeCrude_source_weight_ratio_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) {v₀ : ℝ} (hv₀ : 1 ≤ v₀) :
    markedRawMemorySchurWeight v₀ s.2.2/markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ s choice) ≤
      v₀^(Fintype.card J) := by
  have hvpos : 0 < v₀ := zero_lt_one.trans_le hv₀
  calc
    _ = (markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ s choice)/
        markedRawMemorySchurWeight v₀ s.2.2)⁻¹ := by rw [inv_div]
    _ = ∏ j, v₀^(markedRawEdgePromotionDeletion choice.promotions j).card/
        v₀^((markedRawEdgeStoreSizes hZ s choice).1 j:ℕ) := by
      rw [markedRawEdgeTargetMemory,markedRawGhost_target_weight_ratio hvpos.ne',← Finset.prod_inv_distrib]
      simp only [inv_div]
    _ ≤ ∏ _j : J,v₀ := by
      apply Finset.prod_le_prod₀
      · intro j _
        exact div_nonneg (pow_nonneg hvpos.le _) (pow_nonneg hvpos.le _)
      · intro j _
        have hd : (markedRawEdgePromotionDeletion choice.promotions j).card ≤ 1 := by
          change (choice.promotions j).toFinset.card ≤ 1
          cases choice.promotions j <;> simp
        calc
          _ ≤ v₀^(markedRawEdgePromotionDeletion choice.promotions j).card/1 :=
            div_le_div_of_nonneg_left (pow_nonneg hvpos.le _) zero_lt_one (one_le_pow₀ hv₀)
          _ ≤ v₀ := by
            rw [div_one]
            simpa only [pow_one] using pow_le_pow_right₀ hv₀ hd
    _ = _ := by simp

/-- Full actual weighted row, retaining the choice-dependent factor inside
the norm. The sum includes every admissible store and promotion pattern. -/
def markedRawEdgeCrudeWeightedAbsRow {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ v₀ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z)
    (modifier : MarkedRawEdgeChoice hZ s → ℂ) : ℝ :=
  ∑ choice : MarkedRawEdgeChoice hZ s,
    markedRawEdgeChoicePrimeMass ν V hZ s choice*
      ‖modifier choice*markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s choice‖*
      (markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ s choice)/
        markedRawMemorySchurWeight v₀ s.2.2)

theorem markedRawEdgeCrude_weighted_row_le_unweighted {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p,0 ≤ ν j p) (hV : ∀ j,0 < V j)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ v₀ : ℝ) (hv₀ : 1 ≤ v₀)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z)
    (modifier : MarkedRawEdgeChoice hZ s → ℂ) {L : ℝ} (hL : 0 ≤ L)
    (hmodifier : ∀ choice,‖modifier choice‖ ≤ L) :
    markedRawEdgeCrudeWeightedAbsRow ν V hZ ψ η d₀ Y Q ρ v₀ χ s modifier ≤
      (L*v₀^(Fintype.card J))*markedRawEdgeCrudeAbsRow ν V hZ ψ η d₀ Y Q ρ χ s := by
  classical
  have hvpos : 0 < v₀ := zero_lt_one.trans_le hv₀
  unfold markedRawEdgeCrudeWeightedAbsRow markedRawEdgeCrudeAbsRow
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro choice _
  have hm := markedDirtyRawEdge_prime_mass_nonneg ν V hν hV hZ s choice
  have hnorm : ‖modifier choice*markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s choice‖ ≤
      L*‖markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s choice‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hmodifier choice) (norm_nonneg _)
  have hw : 0 ≤ markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ s choice)/
      markedRawMemorySchurWeight v₀ s.2.2 :=
    div_nonneg (markedRawMemorySchurWeight_pos hvpos _).le (markedRawMemorySchurWeight_pos hvpos _).le
  calc
    _ ≤ (markedRawEdgeChoicePrimeMass ν V hZ s choice*
        (L*‖markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s choice‖))*v₀^(Fintype.card J) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hnorm hm)
        (markedDirtyRawEdge_target_weight_ratio_le hZ s choice hv₀) hw
        (mul_nonneg hm (mul_nonneg hL (norm_nonneg _)))
    _ = _ := by ring

/-- Unconditional crude bound on the full weighted literal edge row.
Only the proved determinant geometry and finite indexed choices are used. -/
theorem markedRawEdgeCrude_weighted_row_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p,0 ≤ ν j p) (hV : ∀ j,0 < V j) {C N : ℝ}
    (hC : 1 ≤ C) (hVC : ∀ j,(V j)⁻¹ ≤ C) (hN : 1 ≤ N) (hνN : ∀ j,(∑ p,ν j p) ≤ N)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (r d₀ Y Q ρ H W A v₀ : ℝ)
    (hY : 0 < Y) (hQ : 0 ≤ Q) (hA : 0 ≤ A) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (hH : 0 ≤ H) (hW : 0 ≤ W) (hv₀ : 1 ≤ v₀)
    (hη : ∀ t,‖η t‖ ≤ H) (hψ : ∀ t,‖ψ t‖ ≤ W) (hsupp : ∀ t,ψ t ≠ 0 → |t| ≤ A)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (hχ : ∀ s,‖χ s‖ ≤ 1)
    (s : MarkedRawState P (pads+1) B Z) (w : ℤ × ℤ) (hw : markedMinorIntegerDet s.1.1 w=1)
    (hτ : markedMinorIntegerTau r s.1.1 ≠ 0)
    (hbox : ∀ v ∈ Z,|markedMinorIntegerTau r v/markedMinorIntegerTau r s.1.1| ≤ 16)
    (modifier : MarkedRawEdgeChoice hZ s → ℂ) {L : ℝ} (hL : 0 ≤ L)
    (hmodifier : ∀ choice,‖modifier choice‖ ≤ L) :
    markedRawEdgeCrudeWeightedAbsRow ν V hZ ψ η d₀ Y Q ρ v₀ χ s modifier ≤
      (L*v₀^(Fintype.card J))*(4*C*N)^(Fintype.card J)*(B+1:ℝ)^(Fintype.card J)*H^2*
        (33*W*(1+(2*A*Y+1)*(4*Q^3/Y))) := by
  have hr := markedRawEdgeCrude_row_le ν V hν hV hC hVC hN hνN hZ ψ η r d₀ Y Q ρ H W A
    hY hQ hA hρ₀ hρ₁ hH hW hη hψ hsupp χ hχ s w hw hτ hbox
  exact (markedRawEdgeCrude_weighted_row_le_unweighted ν V hν hV hZ ψ η d₀ Y Q ρ v₀ hv₀
    χ s modifier hL hmodifier).trans ((mul_le_mul_of_nonneg_left hr
      (mul_nonneg hL (pow_nonneg (zero_le_one.trans hv₀) _))).trans_eq (by ring))

/-- The full row has polynomial dependence on Q, uniformly in Y ≥ 1. -/
theorem markedRawEdgeCrude_weighted_row_le_polynomial {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p,0 ≤ ν j p) (hV : ∀ j,0 < V j) {C N : ℝ}
    (hC : 1 ≤ C) (hVC : ∀ j,(V j)⁻¹ ≤ C) (hN : 1 ≤ N) (hνN : ∀ j,(∑ p,ν j p) ≤ N)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (r d₀ Y Q ρ H W A v₀ : ℝ)
    (hY : 1 ≤ Y) (hQ : 1 ≤ Q) (hA : 0 ≤ A) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (hH : 0 ≤ H) (hW : 0 ≤ W) (hv₀ : 1 ≤ v₀)
    (hη : ∀ t,‖η t‖ ≤ H) (hψ : ∀ t,‖ψ t‖ ≤ W) (hsupp : ∀ t,ψ t ≠ 0 → |t| ≤ A)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (hχ : ∀ s,‖χ s‖ ≤ 1)
    (s : MarkedRawState P (pads+1) B Z) (w : ℤ × ℤ) (hw : markedMinorIntegerDet s.1.1 w=1)
    (hτ : markedMinorIntegerTau r s.1.1 ≠ 0)
    (hbox : ∀ v ∈ Z,|markedMinorIntegerTau r v/markedMinorIntegerTau r s.1.1| ≤ 16)
    (modifier : MarkedRawEdgeChoice hZ s → ℂ) {L : ℝ} (hL : 0 ≤ L)
    (hmodifier : ∀ choice,‖modifier choice‖ ≤ L) :
    markedRawEdgeCrudeWeightedAbsRow ν V hZ ψ η d₀ Y Q ρ v₀ χ s modifier ≤
      (L*v₀^(Fintype.card J))*(4*C*N)^(Fintype.card J)*(B+1:ℝ)^(Fintype.card J)*H^2*
        (33*W*(8*A+5))*Q^3 := by
  have hr := markedRawEdgeCrude_weighted_row_le ν V hν hV hC hVC hN hνN hZ ψ η r d₀ Y Q ρ H W A v₀
    (zero_lt_one.trans_le hY) (zero_le_one.trans hQ) hA hρ₀ hρ₁ hH hW hv₀
    hη hψ hsupp χ hχ s w hw hτ hbox modifier hL hmodifier
  apply hr.trans
  have hp : 0 ≤ (L*v₀^(Fintype.card J))*(4*C*N)^(Fintype.card J)*(B+1:ℝ)^(Fintype.card J)*H^2 := by
    have hC₀ : 0 ≤ C := zero_le_one.trans hC
    have hN₀ : 0 ≤ N := zero_le_one.trans hN
    have hv₀₀ : 0 ≤ v₀ := zero_le_one.trans hv₀
    positivity
  exact (mul_le_mul_of_nonneg_left (markedRawEdgeCrude_kernel_factor_le_polynomial hY hQ hW) hp).trans_eq
    (by ring)

end ArtinMatthews
