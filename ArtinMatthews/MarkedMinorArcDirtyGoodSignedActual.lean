module

public import ArtinMatthews.MarkedMinorArcDirtyGoodDeltaRow
public import ArtinMatthews.MarkedMinorArcDirtyPromotedRow


set_option backward.privateInPublic true
@[expose] public section

/-! Actual full minor rows: the delta root condition and source
injectivity are discharged by the literal good and physical cutoffs. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators

theorem markedDirty_good_signed_fixed_row_eventually
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (hinj : Function.Injective e)
    (I : Finset J) (hI : I.Nonempty) :
    ∀ᶠ x : ℝ in atTop, ∀ (pads B : ℕ) (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
      (r d₀ Y Q q ρ H W v₀ c T A L : ℝ) (w : Z → ℤ × ℤ)
      (χ : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ)
      (s : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z)
      (modifier : (σ : J → Equiv.Perm (Fin (pads+1))) → MarkedRawEdgeChoice hZ (markedRawSlotEquiv σ s) → ℂ),
      1 ≤ B → 1 ≤ Y → 0 ≤ Q → 0 ≤ q → q ≤ 1 → 0 ≤ ρ → ρ < 1 →
      0 ≤ H → 0 ≤ W → 1 ≤ v₀ → 0 < c → 0 ≤ T → 0 ≤ L →
      (∀ t,‖η t‖ ≤ H) → (∀ t,‖ψ t‖ ≤ W) → Function.support ψ ⊆ Set.Icc (-A) A →
      (∀ z,markedMinorIntegerDet z.1 (w z)=1) →
      (∀ z ∈ Z,c ≤ |markedMinorIntegerTau r z| ∧ |markedMinorIntegerTau r z| ≤ T) →
      (∀ z v : Z,|markedMinorIntegerTau r v.1/markedMinorIntegerTau r z.1| ≤ 16) →
      (∀ s,‖χ s‖ ≤ 1) → (∀ σ c,‖modifier σ c‖ ≤ L) →
      markedDirtySignedFixedWeightedRow (markedRawActualPrimeAtom e q x)
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hZ ψ η r d₀ Y Q ρ v₀ w
        (markedRawDirtySecondGoodCutoff e x r w χ) s I modifier ≤
      L*((v₀^(Fintype.card J)*markedDirtyActualRowConstant (Fintype.card J) ρ H W)*
        ((B:ℝ)*(pads+1:ℝ)⁻¹^(Fintype.card J)+(B:ℝ)^(Fintype.card J)*
          Real.exp (-((Real.log x)^(1/10:ℝ))/4))+
        markedDirtyMajorActualConstant (Fintype.card J) v₀ H W c T A*(B+1:ℝ)^(Fintype.card J)*Q^3*
          (Real.exp (-((Real.log x)^(1/10:ℝ)))+Y^(-1/10:ℝ))) := by
  classical
  have hI' := hI
  obtain ⟨jstar,hj⟩ := hI'
  filter_upwards [markedDirty_good_delta_weighted_row_eventually e he hinj I hI,
    markedDirtyMajor_actual_weighted_row_eventually e he I ⟨jstar,hj⟩,
    markedDirty_actual_band_transfer_eventually e he] with x hdelta hmajor htransfer
  intro pads B Z hZ ψ η r d₀ Y Q q ρ H W v₀ c T A L w χ s modifier
    hB hY hQ hq₀ hq₁ hρ₀ hρ₁ hH hW hv₀ hc hT hL hη hψ hsupp hw hτ hbox hχ hmodifier
  have ht := htransfer q hq₀ hq₁
  let χ₂ := markedRawDirtySecondGoodCutoff e x r w χ
  have hχ₂ : ∀ s,‖χ₂ s‖ ≤ 1 := markedRawDirtySecondGoodCutoff_norm_le e x r w χ hχ
  have hsrc : markedMinorIntegerTau r s.1.1 ≠ 0 := by
    intro hz
    have hh := (hτ s.1.1 s.1.2).1
    rw [hz,abs_zero] at hh
    linarith
  have hd := hdelta pads B Z hZ ψ η r d₀ Y q ρ H W v₀ w χ s hv₀ hB hq₀ hq₁ hρ₀ hρ₁
    hH hW hη hψ hχ (hw s.1) hsrc (fun v hv => hbox s.1 ⟨v,hv⟩)
  have hm := hmajor pads B Z hZ η ψ r d₀ Y Q q ρ v₀ c T A H W w χ₂ s
    hY hQ hq₀ hq₁ hc hT hρ₀ hρ₁.le hv₀ hH hW hη hψ hsupp hw hτ hχ₂
  have hsplit := markedDirtySignedFixedWeightedRow_le_delta_add_major
    (markedRawActualPrimeAtom e q x) (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
    ht.1 (fun j => (ht.2.1 j).1) hZ ψ η r d₀ Y Q ρ v₀ (zero_lt_one.trans_le hv₀) w χ₂ s I
    (fun _ _ => 1) (by intros; simp)
  have hmod := markedDirtySignedFixedWeightedRow_modifier_le
    (markedRawActualPrimeAtom e q x) (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
    ht.1 (fun j => (ht.2.1 j).1) hZ ψ η r d₀ Y Q ρ v₀ (zero_lt_one.trans_le hv₀) w χ₂ s I
    modifier hmodifier
  exact hmod.trans (mul_le_mul_of_nonneg_left (hsplit.trans (add_le_add hd hm)) hL)

end
end ArtinMatthews
