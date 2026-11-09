module

public import ArtinMatthews.MarkedMinorArcRawEdgeChargeModifier
public import ArtinMatthews.MarkedMinorArcRawEdgeCrudeWeighted
public import ArtinMatthews.MarkedMinorArcRawEdgeJointReverse


set_option backward.privateInPublic true
@[expose] public section

/-! Literal charged weighted rows. All indexed choices, physical endpoint
tests, true memory caps and target/source Schur ratios remain in the sum. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

def markedRawEdgeChargedWeightedAbsRow {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (K : MarkedRawState P (pads+1) B Z → MarkedRawState P (pads+1) B Z → ℂ)
    (v₀ : ℝ) (s : MarkedRawState P (pads+1) B Z)
    (modifier : MarkedRawEdgeChoice hZ s → ℂ) : ℝ :=
  ∑ c : MarkedRawEdgeChoice hZ s,
    ‖markedRawEdgeChoiceCharge δ γ hZ s c*markedRawEdgeChoiceFreshMass ν hZ s c*
      modifier c*K s (markedRawEdgeTargetState hZ s c)‖*
      (markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ s c)/
        markedRawMemorySchurWeight v₀ s.2.2)

/-- The arbitrary charged row is exactly the previously bounded literal
row with its explicit relative multiplier, not a new comparison kernel. -/
theorem markedRawEdgeChargedWeightedAbsRow_eq_crude {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (δ γ : J → ℂ)
    (hν : ∀ j p,0 ≤ ν j p) (hV : ∀ j,0 < V j)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ v₀ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z)
    (modifier : MarkedRawEdgeChoice hZ s → ℂ) :
    markedRawEdgeChargedWeightedAbsRow ν δ γ hZ
      (markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ) v₀ s modifier =
      markedRawEdgeCrudeWeightedAbsRow ν V hZ ψ η d₀ Y Q ρ v₀ χ s
        (fun c => markedRawEdgeChoiceChargeMultiplier V δ γ hZ s c*modifier c) := by
  classical
  unfold markedRawEdgeChargedWeightedAbsRow markedRawEdgeCrudeWeightedAbsRow
  apply Finset.sum_congr rfl
  intro c _
  rw [markedRawEdgeChoiceCharge_factor ν V δ γ (fun j => (hV j).ne') hZ s c,
    markedRawEdgeChoiceCoefficient_eq_joint]
  have hm := markedDirtyRawEdge_prime_mass_nonneg ν V hν hV hZ s c
  simp only [norm_mul,Complex.norm_real,Real.norm_of_nonneg hm]
  ring

theorem markedRawEdgeChargedWeightedAbsRow_eq_fresh {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    (hν : ∀ j p,0 ≤ ν j p)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ v₀ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z)
    (modifier : MarkedRawEdgeChoice hZ s → ℂ) :
    markedRawEdgeChargedWeightedAbsRow ν δ γ hZ
      (markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ) v₀ s modifier =
      markedRawEdgeCrudeWeightedAbsRow ν (fun _ => 1) hZ ψ η d₀ Y Q ρ v₀ χ s
        (fun c => markedRawEdgeChoiceCharge δ γ hZ s c*modifier c) := by
  simpa only [markedRawEdgeChoiceChargeMultiplier_one] using
    markedRawEdgeChargedWeightedAbsRow_eq_crude ν (fun _ => 1) δ γ hν
      (fun _ => by norm_num) hZ ψ η d₀ Y Q ρ v₀ χ s modifier

/-- Arbitrary complex charges cost only their explicit finite product
bound. No weighted row or target count is supplied as a premise. -/
theorem markedRawEdgeCharged_weighted_row_le_polynomial {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    (hν : ∀ j p,0 ≤ ν j p) {D G N : ℝ} (hD : 1 ≤ D) (hG : 1 ≤ G) (hN : 1 ≤ N)
    (hδ : ∀ j,‖δ j‖ ≤ D) (hγ : ∀ j,‖γ j‖ ≤ G) (hνN : ∀ j,(∑ p,ν j p) ≤ N)
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
    (hmodifier : ∀ c,‖modifier c‖ ≤ L) :
    markedRawEdgeChargedWeightedAbsRow ν δ γ hZ
      (markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ) v₀ s modifier ≤
      (L*v₀^(Fintype.card J))*(4*N*D*G)^(Fintype.card J)*(B+1:ℝ)^(Fintype.card J)*H^2*
        (33*W*(8*A+5))*Q^3 := by
  rw [markedRawEdgeChargedWeightedAbsRow_eq_fresh ν δ γ hν]
  have hDG : 0 ≤ D*G := mul_nonneg (zero_le_one.trans hD) (zero_le_one.trans hG)
  have hm : ∀ c : MarkedRawEdgeChoice hZ s,
      ‖markedRawEdgeChoiceCharge δ γ hZ s c*modifier c‖ ≤ (D*G)^(Fintype.card J)*L := by
    intro c
    rw [norm_mul]
    exact mul_le_mul (markedRawEdgeChoiceCharge_norm_le δ γ hD hG hδ hγ hZ s c)
      (hmodifier c) (norm_nonneg _) (pow_nonneg hDG _)
  have hr := markedRawEdgeCrude_weighted_row_le_polynomial ν (fun _ => 1) hν
    (fun _ => by norm_num) (by norm_num : (1:ℝ) ≤ 1) (fun _ => by norm_num)
    hN hνN hZ ψ η r d₀ Y Q ρ H W A v₀ hY hQ hA hρ₀ hρ₁ hH hW hv₀
    hη hψ hsupp χ hχ s w hw hτ hbox (fun c => markedRawEdgeChoiceCharge δ γ hZ s c*modifier c)
    (mul_nonneg (pow_nonneg hDG _) hL) hm
  exact hr.trans_eq (by simp only [mul_pow]; ring)

end
end ArtinMatthews
