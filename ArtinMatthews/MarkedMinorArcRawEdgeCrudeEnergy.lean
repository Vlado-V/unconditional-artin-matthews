module

public import ArtinMatthews.MarkedMinorArcRawEdgeEnergyBound
public import ArtinMatthews.MarkedMinorArcRawEdgeChargedActual


set_option backward.privateInPublic true
@[expose] public section

/-! The full literal edge has a concrete crude energy bound on the actual
symmetric factorial state space. Both Schur rows are proved here from
the arithmetic row endpoints; neither is a hypothesis of this theorem. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators

theorem markedRawEdgeApply_actual_crude_energy_eventually
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j)
    (hinj : Function.Injective e) :
    ∀ᶠ x : ℝ in atTop, ∀ (pads B : ℕ) (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
      (r d₀ Y Q q ρ H W A v₀ : ℝ) (w : Z → ℤ × ℤ)
      (χ f : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ),
      1 ≤ Y → 1 ≤ Q → 0 ≤ q → q ≤ 1 → 0 ≤ ρ → ρ ≤ 1 →
      0 ≤ H → 0 ≤ W → 0 ≤ A → 1 ≤ v₀ →
      (∀ t,‖η t‖ ≤ H) → (∀ t,‖ψ t‖ ≤ W) → (∀ t,ψ t ≠ 0 → |t| ≤ A) →
      (∀ s,‖χ s‖ ≤ 1) →
      (∀ z active,MarkedRawMemorySymmetric (fun m => χ (z,(active,m)))) →
      (∀ z active,MarkedRawMemorySymmetric (fun m => f (z,(active,m)))) →
      (∀ z,markedMinorIntegerDet z.1 (w z)=1) →
      (∀ z : Z,markedMinorIntegerTau r z.1 ≠ 0) →
      (∀ z v : Z,|markedMinorIntegerTau r v.1/markedMinorIntegerTau r z.1| ≤ 16) →
      (∑ s,markedRawStateMass (markedRawActualPrimeAtom e q x) s*
        ‖markedRawEdgeApply (markedRawActualPrimeAtom e q x)
          (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hZ ψ η d₀ Y Q ρ χ f s‖^2) ≤
        (markedRawEdgeCrudeActualConstant (Fintype.card J) v₀ H W A 1*(B+1:ℝ)^(Fintype.card J)*Q^3)^2*
          ∑ s,markedRawStateMass (markedRawActualPrimeAtom e q x) s*‖f s‖^2 := by
  filter_upwards [markedRawEdgeCrude_actual_weighted_row_eventually e he,
    markedRawEdgeCharged_actual_reverse_row_eventually e he hinj,
    markedDirty_actual_band_transfer_eventually e he] with x hrow hcolumn htransfer
  intro pads B Z hZ ψ η r d₀ Y Q q ρ H W A v₀ w χ f hY hQ hq₀ hq₁ hρ₀ hρ₁
    hH hW hA hv₀ hη hψ hsupp hχnorm hχ hf hw hτ hbox
  let R := markedRawEdgeCrudeActualConstant (Fintype.card J) v₀ H W A 1*(B+1:ℝ)^(Fintype.card J)*Q^3
  have hR : 0 ≤ R := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hv₀₀ : 0 ≤ v₀ := zero_le_one.trans hv₀
    have hQ₀ : 0 ≤ Q := zero_le_one.trans hQ
    dsimp [R,markedRawEdgeCrudeActualConstant]
    positivity
  have hr : ∀ s,markedRawEdgeCrudeWeightedAbsRow (markedRawActualPrimeAtom e q x)
      (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hZ ψ η d₀ Y Q ρ v₀ χ s (fun _ => 1) ≤ R := by
    intro s
    exact hrow pads B Z hZ ψ η r d₀ Y Q q ρ H W A v₀ 1 χ s (w s.1) (fun _ => 1)
      hY hQ hq₀ hq₁ hρ₀ hρ₁ hH hW hA hv₀ zero_le_one hη hψ hsupp hχnorm
      (by intro; simp) (hw s.1) (hτ s.1) (fun v hv => hbox s.1 ⟨v,hv⟩)
  have hc : ∀ s,markedRawEdgeChargedWeightedAbsRow (markedRawActualPrimeAtom e q x)
      (fun _ => 1) (fun j => ((bandReciprocalMass (markedLogPowerBand (e j) x))⁻¹:ℝ)) hZ
      (fun target source => markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ source target)
      v₀ s (fun _ => 1) ≤ R := by
    intro s
    exact hcolumn pads B Z hZ ψ η r d₀ Y Q q ρ H W A v₀ 1 χ s (w s.1) (fun _ => 1)
      hY hQ hq₀ hq₁ hρ₀ hρ₁ hH hW hA hv₀ zero_le_one hη hψ hsupp hχnorm
      (by intro; simp) (hw s.1) (hτ s.1) (fun v hv => hbox s.1 ⟨v,hv⟩)
  have ht := htransfer q hq₀ hq₁
  exact markedRawEdgeApply_energy_le_of_rows (markedRawActualPrimeAtom e q x)
    (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) ht.1 (fun j => (ht.2.1 j).1)
    hZ ψ η d₀ Y Q ρ (zero_lt_one.trans_le hv₀) hR χ f hχ hf hr hc

end
end ArtinMatthews
