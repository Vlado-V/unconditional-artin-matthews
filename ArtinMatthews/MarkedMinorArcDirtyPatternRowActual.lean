module

public import ArtinMatthews.MarkedMinorArcRawEdgePatternFilteredRows
public import ArtinMatthews.MarkedMinorArcDirtyGoodLogSaving
public import ArtinMatthews.MarkedMinorArcDirtySwapBound


set_option backward.privateInPublic true
@[expose] public section

/-! Exact actual-pattern interfaces for the proved arithmetic rows. The
coefficient family may contain any bounded sector or endpoint modifier. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators

theorem markedDirty_pattern_promoted_row_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (hinj : Function.Injective e)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (v₀ c T A H W ρ L A₀ G : ℝ)
    (hv₀ : 1 ≤ v₀) (hc : 0 < c) (hT : 0 ≤ T) (hH : 0 ≤ H) (hW : 0 ≤ W)
    (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) (hL : 0 ≤ L) (hdepth : 100*(G+2)<(Fintype.card J:ℝ))
    (hη : ∀ t,‖η t‖ ≤ H) (hψ : ∀ t,‖ψ t‖ ≤ W) (hsupp : Function.support ψ ⊆ Set.Icc (-A) A) :
    ∀ᶠ x : ℝ in atTop, ∀ (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
      (r d₀ Y q : ℝ) (w : Z → ℤ × ℤ)
      (χ : MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x) (markedDirtyMemoryCutoff x) Z → ℂ)
      (β : MarkedRawEdgePatternKernel (markedRawActualPrimeBand e x)
        ⌊(Real.log x)^(1/100:ℝ)⌋₊ (markedDirtyMemoryCutoff x) Z)
      (s : MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x) (markedDirtyMemoryCutoff x) Z),
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y → 0 ≤ q → q ≤ 1 →
      (∀ z,markedMinorIntegerDet z.1 (w z)=1) →
      (∀ z ∈ Z,c ≤ |markedMinorIntegerTau r z| ∧ |markedMinorIntegerTau r z| ≤ T) →
      (∀ z v : Z,|markedMinorIntegerTau r v.1/markedMinorIntegerTau r z.1| ≤ 16) →
      (∀ s,‖χ s‖ ≤ 1) → (∀ p q s t,‖β p q s t‖ ≤ L) →
      markedRawSlotAverageReal
        (markedRawEdgePatternWeightedRow (markedRawActualPrimeAtom e q x)
          (fun j => ((bandReciprocalMass (markedLogPowerBand (e j) x))⁻¹:ℝ)) (fun _ => 1) hZ
          (markedRawEdgePromotedKernel (fun p q u v => β p q u v *
            markedRawEdgeJointCoefficient hZ ψ η d₀ Y ((Real.log x)^A₀) ρ
              (markedRawDirtyGoodCutoff e x r d₀ Y w χ) u v)) v₀) s ≤ (Real.log x)^(-G) := by
  filter_upwards [markedDirty_good_promoted_row_log_saving e he hinj ψ η v₀ c T A H W ρ L A₀ G
      hv₀ hc hT hH hW hρ₀ hρ₁ hL hdepth hη hψ hsupp,
    markedDirty_actual_band_transfer_eventually e he] with x hrow htransfer
  intro Z hZ r d₀ Y q w χ β s hY hq₀ hq₁ hw hτ hbox hχ hβ
  have ht := htransfer q hq₀ hq₁
  refine (markedRawEdgePattern_promoted_average_eq
    (markedRawActualPrimeAtom e q x) (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
    ht.1 (fun j => (ht.2.1 j).1) hZ ψ η r d₀ Y ((Real.log x)^A₀) ρ v₀ w
    (markedRawDirtySecondGoodCutoff e x r w χ) β s).le.trans ?_
  exact hrow Z hZ r d₀ Y q w χ s _ hY hq₀ hq₁ hw hτ hbox hχ
    (fun σ c => hβ _ _ _ _)

theorem markedDirty_pattern_noPromotion_row_crude
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ (pads B : ℕ) (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
      (r d₀ Y Q q ρ H W A v₀ L : ℝ)
      (χ : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ)
      (β : MarkedRawEdgePatternKernel (markedRawActualPrimeBand e x) pads B Z)
      (s : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z) (w : ℤ × ℤ),
      1 ≤ Y → 1 ≤ Q → 0 ≤ q → q ≤ 1 → 0 ≤ ρ → ρ ≤ 1 → 0 ≤ H → 0 ≤ W → 0 ≤ A → 1 ≤ v₀ → 0 ≤ L →
      (∀ t,‖η t‖ ≤ H) → (∀ t,‖ψ t‖ ≤ W) → (∀ t,ψ t ≠ 0 → |t| ≤ A) →
      (∀ s,‖χ s‖ ≤ 1) → (∀ p q s t,‖β p q s t‖ ≤ L) → markedMinorIntegerDet s.1.1 w=1 →
      markedMinorIntegerTau r s.1.1 ≠ 0 →
      (∀ v ∈ Z,|markedMinorIntegerTau r v/markedMinorIntegerTau r s.1.1| ≤ 16) →
      markedRawSlotAverageReal
        (markedRawEdgePatternWeightedRow (markedRawActualPrimeAtom e q x)
          (fun j => ((bandReciprocalMass (markedLogPowerBand (e j) x))⁻¹:ℝ)) (fun _ => 1) hZ
          (markedRawEdgeNoPromotionKernel (fun p q u v => β p q u v *
            markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ u v)) v₀) s ≤
        markedRawEdgeNoPromotionConstant (Fintype.card J) v₀ H W A L*Q^3 := by
  filter_upwards [markedRawEdgeNoPromotion_actual_sym_row_eventually e he,
    markedDirty_actual_band_transfer_eventually e he] with x hrow htransfer
  intro pads B Z hZ ψ η r d₀ Y Q q ρ H W A v₀ L χ β s w
    hY hQ hq₀ hq₁ hρ₀ hρ₁ hH hW hA hv₀ hL hη hψ hsupp hχ hβ hw hτ hbox
  have ht := htransfer q hq₀ hq₁
  rw [markedRawEdgePattern_noPromotion_average_eq
    (markedRawActualPrimeAtom e q x) (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
    ht.1 (fun j => (ht.2.1 j).1)]
  exact hrow pads B Z hZ ψ η r d₀ Y Q q ρ H W A v₀ L χ s w _
    hY hQ hq₀ hq₁ hρ₀ hρ₁ hH hW hA hv₀ hL hη hψ hsupp hχ
    (fun σ c => hβ _ _ _ _) hw hτ hbox

end
end ArtinMatthews
