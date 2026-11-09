module

public import ArtinMatthews.MarkedMinorArcRawEdgePatternMinorRows
public import ArtinMatthews.MarkedMinorArcDirtySwapBound


set_option backward.privateInPublic true
@[expose] public section

/-! Exact averaged reversal and charge correction for the full minor
kernel, with a bound on every Boolean charge pattern. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators

theorem markedRawEdgeFlagChargeSwap_norm_le {J : Type*} [Fintype J]
    (V : J → ℝ) (hV : ∀ j,0 < V j) {C : ℝ} (hC : 1 ≤ C)
    (hVC : ∀ j,V j ≤ C) (hiVC : ∀ j,(V j)⁻¹ ≤ C) (p q : J → Bool) :
    ‖markedRawEdgeFlagChargeSwap V p q‖ ≤ C^(Fintype.card J) := by
  unfold markedRawEdgeFlagChargeSwap
  rw [norm_prod]
  calc
    _ ≤ ∏ _j : J,C := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro j _
      have hv : (V j:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hV j).ne'
      by_cases hp : p j
      · by_cases hq : q j
        · simpa [hp,hq,hv] using hC
        · simpa only [hp,hq,Bool.false_eq_true,ite_true,ite_false,mul_one,Complex.norm_real,
            Real.norm_of_nonneg (hV j).le] using hVC j
      · by_cases hq : q j
        · simpa only [hp,hq,Bool.false_eq_true,ite_true,ite_false,one_mul,Complex.norm_real,
            Real.norm_of_nonneg (inv_pos.mpr (hV j)).le] using hiVC j
        · simpa [hp,hq] using hC
    _ = _ := by simp

theorem markedRawEdgeFlagChargeSwap_actual_bound_eventually
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop,∀ q : ℝ,0 ≤ q → q ≤ 1 → ∀ p s : J → Bool,
      ‖markedRawEdgeFlagChargeSwap (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) p s‖ ≤
        (2/Real.log 2)^(Fintype.card J) := by
  have hb := eventually_all.mpr (fun j => marked_log_power_band_mass_eventually
    (show 0 < e j by linarith [he j]))
  filter_upwards [hb,markedDirty_actual_band_transfer_eventually e he] with x hband htransfer
  intro q hq₀ hq₁ p s
  have ht := htransfer q hq₀ hq₁
  exact markedRawEdgeFlagChargeSwap_norm_le _ (fun j => (ht.2.1 j).1)
    markedDirty_transfer_constant_one_le
    (fun j => (hband j).2.le.trans markedDirty_transfer_constant_one_le)
    (fun j => (ht.2.1 j).2) p s

theorem markedRawEdgePatternWeightedAverage_minor_reverse
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j))) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ v₀ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (β : MarkedRawEdgePatternKernel P pads B Z)
    (s : MarkedRawState P (pads+1) B Z) :
    markedRawSlotAverageReal (markedRawEdgePatternWeightedRow ν δ γ hZ
      (markedRawEdgePatternReverse (fun p q u v => β p q u v*markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ u v)) v₀) s =
    markedRawSlotAverageReal (markedRawEdgePatternWeightedRow ν δ γ hZ
      (fun p q u v => markedRawEdgePatternReverse β p q u v*
        markedRawEdgeJointCoefficient hZ (markedRawEdgeReflectedCutoff ψ) η d₀ Y Q ρ χ u v) v₀) s := by
  unfold markedRawSlotAverageReal
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  exact markedRawEdgePatternWeightedRow_minor_reverse ν δ γ hdisj hZ ψ η d₀ Y Q ρ v₀ χ β _

theorem markedRawEdgePatternWeightedAverage_minor_swap
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (hV : ∀ j,V j ≠ 0)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ v₀ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (β : MarkedRawEdgePatternKernel P pads B Z)
    (s : MarkedRawState P (pads+1) B Z) :
    markedRawSlotAverageReal (markedRawEdgePatternWeightedRow ν (fun _ => 1) (fun j => ((V j)⁻¹:ℝ)) hZ
      (fun p q u v => β p q u v*markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ u v) v₀) s =
    markedRawSlotAverageReal (markedRawEdgePatternWeightedRow ν (fun j => ((V j)⁻¹:ℝ)) (fun _ => 1) hZ
      (fun p q u v => (markedRawEdgeFlagChargeSwap V p q*β p q u v)*
        markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ u v) v₀) s := by
  unfold markedRawSlotAverageReal
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  simpa only [mul_assoc] using markedRawEdgePatternWeightedRow_swap ν V hV hZ
    (fun p q u v => β p q u v*markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ u v) v₀ (markedRawSlotEquiv σ s)

end
end ArtinMatthews
