module

public import ArtinMatthews.MarkedMinorArcRawEdgeConditionalPolynomial
public import ArtinMatthews.MarkedMinorArcRawEdgeCrudeActual


set_option backward.privateInPublic true
@[expose] public section

/-! Actual tilted-band specialization of the conditional full edge row.
Only the explicit finite fresh-tuple cost remains as an input to this
arithmetic adapter; target geometry and every other row factor are proved. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedRawEdgeConditional_actual_weighted_row_eventually
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ (pads B : ℕ) (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
      (r d₀ Y Q q ρ H W A v₀ D : ℝ)
      (χ : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ)
      (s : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z) (w : ℤ × ℤ)
      (gate : MarkedRawEdgeChoice hZ s → Prop)
      (freshGate : (I : Finset J) → (J → Bool) → MarkedRawPromotionTuple s.2.2 I →
        ((j : ↥(Finset.univ \ I)) → ↥(markedRawActualPrimeBand e x j.1)) → Prop),
      1 ≤ Y → 1 ≤ Q → 0 ≤ q → q ≤ 1 → 0 ≤ ρ → ρ ≤ 1 →
      0 ≤ H → 0 ≤ W → 0 ≤ A → 1 ≤ v₀ → 0 ≤ D →
      (∀ t, ‖η t‖ ≤ H) → (∀ t, ‖ψ t‖ ≤ W) → (∀ t, ψ t ≠ 0 → |t| ≤ A) →
      (∀ s, ‖χ s‖ ≤ 1) →
      markedMinorIntegerDet s.1.1 w = 1 → markedMinorIntegerTau r s.1.1 ≠ 0 →
      (∀ v ∈ Z, |markedMinorIntegerTau r v/markedMinorIntegerTau r s.1.1| ≤ 16) →
      (∀ I store indices fresh (c : MarkedDirtyFixedEdgeChoice hZ s I),
        c ∈ markedDirtyMajorChoiceFiber hZ s I store indices fresh →
          (gate c.1 ↔ freshGate I store indices fresh)) →
      (∀ I store indices,
        (∑ fresh : (j : ↥(Finset.univ \ I)) → ↥(markedRawActualPrimeBand e x j.1),
          if freshGate I store indices fresh then
            finiteProductMass (fun j : ↥(Finset.univ \ I) => markedRawActualPrimeAtom e q x j.1) fresh
          else 0) ≤ D*(2:ℝ)^(Fintype.card J)) →
      markedRawEdgeConditionalWeightedAbsRow (markedRawActualPrimeAtom e q x)
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hZ ψ η d₀ Y Q ρ v₀ χ s gate ≤
        D*(markedRawEdgeCrudeActualConstant (Fintype.card J) v₀ H W A 1 *
          (B+1:ℝ)^(Fintype.card J)*Q^3) := by
  filter_upwards [markedDirty_actual_band_transfer_eventually e he] with x htransfer
  intro pads B Z hZ ψ η r d₀ Y Q q ρ H W A v₀ D χ s w gate freshGate
    hY hQ hq₀ hq₁ hρ₀ hρ₁ hH hW hA hv₀ hD hη hψ hsupp hχ hw hτ hbox hgate hmass
  have ht := htransfer q hq₀ hq₁
  have hr := markedRawEdge_conditional_weighted_row_le_polynomial (markedRawActualPrimeAtom e q x)
    (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) ht.1 (fun j => (ht.2.1 j).1)
    markedDirty_transfer_constant_one_le (fun j => (ht.2.1 j).2)
    (by norm_num : (0:ℝ) ≤ 2) hD hZ ψ η r d₀ Y Q ρ H W A v₀ hv₀
    hY hQ hA hρ₀ hρ₁ hH hW hη hψ hsupp χ hχ s w hw hτ hbox gate freshGate hgate hmass
  apply hr.trans_eq
  rw [show 4*(2/Real.log 2)*2 = (16/Real.log 2:ℝ) by ring]
  unfold markedRawEdgeCrudeActualConstant
  ring

end ArtinMatthews
