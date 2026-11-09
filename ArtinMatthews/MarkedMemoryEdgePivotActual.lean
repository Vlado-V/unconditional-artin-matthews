module

public import ArtinMatthews.MarkedMemoryEdgePivotMass
public import ArtinMatthews.MarkedMemoryBirthAtom


set_option backward.privateInPublic true
@[expose] public section

/-! Actual full edge rows with the literal chronological pivot gate.
Each selected fresh nonpivot costs one small tilted atom. All target,
store, promotion, memory and geometric restrictions remain in the sum. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedMemoryEdgePivot_actual_weighted_row_eventually
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ (M B N : ℕ)
      (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) (t : Fin N)
      (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes)
      (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
      (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (r d₀ Y Q q ρ H W A v₀ : ℝ)
      (χ : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ)
      (s : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z) (w : ℤ × ℤ),
      1 ≤ Y → 1 ≤ Q → 0 ≤ q → q ≤ 1 → 0 ≤ ρ → ρ ≤ 1 →
      0 ≤ H → 0 ≤ W → 0 ≤ A → 1 ≤ v₀ →
      (∀ u,‖η u‖ ≤ H) → (∀ u,‖ψ u‖ ≤ W) → (∀ u,ψ u≠0 → |u| ≤ A) →
      (∀ s,‖χ s‖ ≤ 1) → markedMinorIntegerDet s.1.1 w=1 →
      markedMinorIntegerTau r s.1.1≠0 →
      (∀ v∈Z,|markedMinorIntegerTau r v/markedMinorIntegerTau r s.1.1| ≤ 16) →
      markedRawEdgeConditionalWeightedAbsRow (markedRawActualPrimeAtom e q x)
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hZ ψ η d₀ Y Q ρ v₀ χ s
        (markedMemoryEdgePivotGate σ t old hZ s) ≤
      (markedMemoryBirthAtomEnvelope x)^(markedMemoryStageNonpivots σ (2*t.1+2)).card*
        (markedRawEdgeCrudeActualConstant (Fintype.card J) v₀ H W A 1*(B+1:ℝ)^(Fintype.card J)*Q^3) := by
  filter_upwards [markedRawEdgeConditional_actual_weighted_row_eventually e he,
    markedMemoryBirthAtom_actual_eventually e he,
    markedRawGhost_actual_band_mass_eventually e he] with x hrow hatom hmass
  intro M B N σ t old pads Z hZ ψ η r d₀ Y Q q ρ H W A v₀ χ s w
    hY hQ hq₀ hq₁ hρ₀ hρ₁ hH hW hA hv₀ hη hψ hsupp hχ hw hτ hbox
  have hν : ∀ j p,0 ≤ markedRawActualPrimeAtom e q x j p := fun j p => (hatom q hq₀ hq₁ j p).1
  apply hrow pads B Z hZ ψ η r d₀ Y Q q ρ H W A v₀
    ((markedMemoryBirthAtomEnvelope x)^(markedMemoryStageNonpivots σ (2*t.1+2)).card)
    χ s w (markedMemoryEdgePivotGate σ t old hZ s)
    (fun I _ _ => markedMemoryEdgePivotFreshGate σ t old I)
    hY hQ hq₀ hq₁ hρ₀ hρ₁ hH hW hA hv₀
    (pow_nonneg (markedMemoryBirthAtomEnvelope_pos x).le _) hη hψ hsupp hχ hw hτ hbox
  · exact markedMemoryEdgePivotGate_fiber σ t old hZ s
  · intro I _ _
    exact markedMemoryEdgePivot_fresh_mass_le (markedRawActualPrimeAtom e q x) hν
      (markedMemoryBirthAtomEnvelope_pos x).le (by norm_num : (1:ℝ) ≤ 2)
      (fun j p => (hatom q hq₀ hq₁ j p).2) (hmass q hq₀ hq₁) σ t old I

end ArtinMatthews
