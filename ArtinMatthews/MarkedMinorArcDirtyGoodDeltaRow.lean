module

public import ArtinMatthews.MarkedMinorArcDirtySecondGood
public import ArtinMatthews.MarkedMinorArcDirtySignedRow


set_option backward.privateInPublic true
@[expose] public section

/-! The actual beta gate supplies the true delta root condition. Physical
endpoint distinctness supplies source injectivity, including zero rows. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators

theorem markedDirtyActualWeightedConstant_nonneg (K : ℕ) {v₀ ρ H W : ℝ}
    (hv₀ : 1 ≤ v₀) (hW : 0 ≤ W) :
    0 ≤ v₀^K*markedDirtyActualRowConstant K ρ H W := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hv : 0 ≤ v₀ := zero_le_one.trans hv₀
  unfold markedDirtyActualRowConstant markedDirtyRawRowConstant
  positivity

theorem markedDirtyGoodDeltaWeightedRow_eq_zero_of_not_second
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (x : ℝ)
    (ν : (j : J) → ↥(markedRawActualPrimeBand e x j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ η : ℝ → ℂ) (r d₀ Y ρ v₀ : ℝ) (w : Z → ℤ × ℤ)
    (χ : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ)
    (s : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z) (I : Finset J)
    (hs : ¬MarkedRawDirtySecondGood e x r w s) :
    markedDirtyRawEdgeDeltaWeightedRow ν V hZ ψ η d₀ Y ρ v₀
      (markedRawDirtyGoodCutoff e x r d₀ Y w χ) s I=0 := by
  apply markedDirtyDeltaWeightedRow_eq_zero_of_source_zero
  intro σ
  apply markedRawDirtyGoodCutoff_eq_zero_of_not_second
  exact fun h => hs ((markedRawDirtySecondGood_slots e x r w s σ).mp h)

theorem markedDirty_good_delta_weighted_row_eventually
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (hinj : Function.Injective e)
    (I : Finset J) (hI : I.Nonempty) :
    ∀ᶠ x : ℝ in atTop, ∀ (pads B : ℕ) (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (ψ η : ℝ → ℂ) (r d₀ Y q ρ H W v₀ : ℝ)
      (w : Z → ℤ × ℤ)
      (χ : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ)
      (s : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z),
      1 ≤ v₀ → 1 ≤ B → 0 ≤ q → q ≤ 1 → 0 ≤ ρ → ρ < 1 → 0 ≤ H → 0 ≤ W →
      (∀ t,‖η t‖ ≤ H) → (∀ t,‖ψ t‖ ≤ W) → (∀ s,‖χ s‖ ≤ 1) →
      markedMinorIntegerDet s.1.1 (w s.1)=1 → markedMinorIntegerTau r s.1.1 ≠ 0 →
      (∀ v ∈ Z,|markedMinorIntegerTau r v/markedMinorIntegerTau r s.1.1| ≤ 16) →
      markedDirtyRawEdgeDeltaWeightedRow (markedRawActualPrimeAtom e q x)
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hZ ψ η d₀ Y ρ v₀
        (markedRawDirtyGoodCutoff e x r d₀ Y w χ) s I ≤
        (v₀^(Fintype.card J)*markedDirtyActualRowConstant (Fintype.card J) ρ H W)*
          ((B:ℝ)*(pads+1:ℝ)⁻¹^(Fintype.card J)+(B:ℝ)^(Fintype.card J)*
            Real.exp (-((Real.log x)^(1/10:ℝ))/4)) := by
  classical
  obtain ⟨jstar,hj,hmax⟩ := Finset.exists_max_image I e hI
  filter_upwards [markedDirtyRawEdge_actual_delta_weighted_row_eventually e he hinj I jstar hj] with x hx
  intro pads B Z hZ ψ η r d₀ Y q ρ H W v₀ w χ s hv₀ hB hq₀ hq₁ hρ₀ hρ₁ hH hW hη hψ hχ hw hτ hbox
  have hbound : 0 ≤ (v₀^(Fintype.card J)*markedDirtyActualRowConstant (Fintype.card J) ρ H W)*
      ((B:ℝ)*(pads+1:ℝ)⁻¹^(Fintype.card J)+(B:ℝ)^(Fintype.card J)*
        Real.exp (-((Real.log x)^(1/10:ℝ))/4)) :=
    mul_nonneg (markedDirtyActualWeightedConstant_nonneg _ hv₀ hW) (by positivity)
  by_cases hg : MarkedRawDirtySecondGood e x r w s
  · by_cases hd : ∀ j,Function.Injective (s.2.1 j)
    · exact hx pads B Z hZ ψ η d₀ Y q ρ H W v₀
        (markedRawDirtyGoodCutoff e x r d₀ Y w χ) s (w s.1) r
        (markedRawDirtyFullTrials e x s.2.1 (I.erase jstar)) hv₀ hB hq₀ hq₁ hρ₀ hρ₁ hH hW hη hψ
        (markedRawDirtyGoodCutoff_norm_le e x r d₀ Y w χ hχ) hd hw hτ hbox
        (markedDirtyRawEdgeTrials_subset_full e x s.2.1 s.2.2 (I.erase jstar)) (hg I jstar hj hmax)
    · rw [markedDirtyDeltaWeightedRow_eq_zero_of_not_distinct _ _ hZ ψ η d₀ Y ρ v₀ _ s I hd]
      exact hbound
  · rw [markedDirtyGoodDeltaWeightedRow_eq_zero_of_not_second e x _ _ hZ ψ η r d₀ Y ρ v₀ w χ s I hg]
    exact hbound

end
end ArtinMatthews
