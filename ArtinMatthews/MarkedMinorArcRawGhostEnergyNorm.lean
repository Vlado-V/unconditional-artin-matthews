module

public import ArtinMatthews.MarkedMinorArcRawGhostEnergyBound


set_option backward.privateInPublic true
@[expose] public section

/-! The square-root weighted L² bound for the literal physical ghost action. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators

/-- The actual ghost has a uniform weighted L² constant with no cutoff or
state-count loss. This is the square root of the proved physical energy inequality. -/
theorem marked_minor_actual_raw_ghost_sqrt_energy
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) {q ρ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hρ : 0 < ρ) (hgap : Real.sqrt q < ρ^2) :
    ∀ᶠ x : ℝ in atTop, ∀ (qStage : ℝ), 0 ≤ qStage → qStage ≤ Real.sqrt q →
      ∀ (M B : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
        (f : MarkedRawState (markedRawActualPrimeBand e x) M B Z → ℂ),
      (∀ z a, MarkedRawMemorySymmetric (fun m => f (z, (a, m)))) →
      Real.sqrt (∑ s, markedRawStateMass (markedRawActualPrimeAtom e q x) s *
        ‖markedRawGhostApply (markedRawActualPrimeAtom e q x)
          (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) qStage ρ hZ f s‖^2) ≤
      Real.exp ((Fintype.card J : ℝ) * (2 * markedRawGhostSchurParameter q ρ / ρ)) *
        Real.sqrt (∑ s, markedRawStateMass (markedRawActualPrimeAtom e q x) s * ‖f s‖^2) := by
  filter_upwards [marked_minor_actual_raw_ghost_energy e he hq₀ hq₁ hρ hgap] with x hx
  intro qStage hqs₀ hqs M B Z hZ f hf
  have hh := Real.sqrt_le_sqrt (hx qStage hqs₀ hqs M B Z hZ f hf)
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.exp_pos _).le] at hh
  exact hh

end
end ArtinMatthews
