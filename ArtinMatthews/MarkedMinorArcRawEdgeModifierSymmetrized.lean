module

public import ArtinMatthews.MarkedMinorArcRawEdgeModifierActual
public import ArtinMatthews.MarkedMinorArcRawEdgeBirthModifier
public import ArtinMatthews.MarkedMinorArcRawEdgeSlotTranspose


set_option backward.privateInPublic true
@[expose] public section

/-! Both literal source/target slot averages around a choice-modified edge
retain the actual crude energy bound. Birth-only local modifiers also
preserve the pending-symmetric domain. -/

namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators

def markedRawEdgeModifiedSymmetrized {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (modifier : (s : MarkedRawState P (pads+1) B Z) → MarkedRawEdgeChoice hZ s → ℂ)
    (f : MarkedRawState P (pads+1) B Z → ℂ) :=
  markedRawSlotAverage (markedRawEdgeModifiedApply ν V hZ ψ η d₀ Y Q ρ χ modifier (markedRawSlotAverage f))

theorem markedRawEdgeBirthModifiedSymmetrized_symmetric
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ f : MarkedRawState P (pads+1) B Z → ℂ)
    (φ : J → Option Nat.Primes → ℂ)
    (hχ : ∀ z a, MarkedRawMemorySymmetric (fun m => χ (z,(a,m))))
    (hf : ∀ z a, MarkedRawMemorySymmetric (fun m => f (z,(a,m))))
    (z : Z) (a : MarkedRawActive P (pads+1)) :
    MarkedRawMemorySymmetric (fun m => markedRawEdgeModifiedSymmetrized ν V hZ ψ η d₀ Y Q ρ χ
      (markedRawEdgeBirthModifier φ) f (z,(a,m))) :=
  markedRawSlotAverage_symmetric _
    (markedRawEdgeBirthModifiedApply_symmetric ν V hZ ψ η d₀ Y Q ρ χ _ φ hχ
      (markedRawSlotAverage_symmetric f hf)) z a

theorem markedRawEdgeModifiedSymmetrized_actual_crude_energy_eventually
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j)
    (hinj : Function.Injective e) :
    ∀ᶠ x : ℝ in atTop, ∀ (pads B : ℕ) (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
      (r d₀ Y Q q ρ H W A v₀ : ℝ) (w : Z → ℤ × ℤ)
      (χ f : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ)
      (modifier : (s : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z) →
        MarkedRawEdgeChoice hZ s → ℂ),
      1 ≤ Y → 1 ≤ Q → 0 ≤ q → q ≤ 1 → 0 ≤ ρ → ρ ≤ 1 →
      0 ≤ H → 0 ≤ W → 0 ≤ A → 1 ≤ v₀ →
      (∀ t,‖η t‖ ≤ H) → (∀ t,‖ψ t‖ ≤ W) → (∀ t,ψ t ≠ 0 → |t| ≤ A) →
      (∀ s,‖χ s‖ ≤ 1) → (∀ s c, ‖modifier s c‖ ≤ 1) →
      (∀ z active,MarkedRawMemorySymmetric (fun m => χ (z,(active,m)))) →
      (∀ z active,MarkedRawMemorySymmetric (fun m => f (z,(active,m)))) →
      (∀ z,markedMinorIntegerDet z.1 (w z)=1) →
      (∀ z : Z,markedMinorIntegerTau r z.1 ≠ 0) →
      (∀ z v : Z,|markedMinorIntegerTau r v.1/markedMinorIntegerTau r z.1| ≤ 16) →
      (∑ s,markedRawStateMass (markedRawActualPrimeAtom e q x) s*
        ‖markedRawEdgeModifiedSymmetrized (markedRawActualPrimeAtom e q x)
          (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hZ ψ η d₀ Y Q ρ χ modifier f s‖^2) ≤
        (markedRawEdgeCrudeActualConstant (Fintype.card J) v₀ H W A 1*(B+1:ℝ)^(Fintype.card J)*Q^3)^2*
          ∑ s,markedRawStateMass (markedRawActualPrimeAtom e q x) s*‖f s‖^2 := by
  filter_upwards [markedRawEdgeModifiedApply_actual_crude_energy_eventually e he hinj,
    markedDirty_actual_band_transfer_eventually e he] with x hraw htransfer
  intro pads B Z hZ ψ η r d₀ Y Q q ρ H W A v₀ w χ f modifier hY hQ hq₀ hq₁ hρ₀ hρ₁
    hH hW hA hv₀ hη hψ hsupp hχnorm hm hχ hf hw hτ hbox
  have hν := (htransfer q hq₀ hq₁).1
  have hr := hraw pads B Z hZ ψ η r d₀ Y Q q ρ H W A v₀ w χ (markedRawSlotAverage f) modifier
    hY hQ hq₀ hq₁ hρ₀ hρ₁ hH hW hA hv₀ hη hψ hsupp hχnorm hm hχ
    (markedRawSlotAverage_symmetric f hf) hw hτ hbox
  let R := markedRawEdgeCrudeActualConstant (Fintype.card J) v₀ H W A 1*(B+1:ℝ)^(Fintype.card J)*Q^3
  calc
    _ ≤ ∑ s, markedRawStateMass (markedRawActualPrimeAtom e q x) s *
        ‖markedRawEdgeModifiedApply (markedRawActualPrimeAtom e q x)
          (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hZ ψ η d₀ Y Q ρ χ modifier
            (markedRawSlotAverage f) s‖^2 := markedRawSlotAverage_energy_le _ hν _
    _ ≤ R^2*∑ s, markedRawStateMass (markedRawActualPrimeAtom e q x) s*‖markedRawSlotAverage f s‖^2 := hr
    _ ≤ _ := mul_le_mul_of_nonneg_left (markedRawSlotAverage_energy_le _ hν f) (sq_nonneg R)

end
end ArtinMatthews
