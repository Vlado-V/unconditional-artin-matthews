module

public import ArtinMatthews.MarkedMinorArcRawGhostEnergyColumn
public import ArtinMatthews.MarkedMinorArcRawGhostSwappedRow


set_option backward.privateInPublic true
@[expose] public section

/-! The full actual ghost energy estimate on the genuine pending-symmetric
space. The constant depends on the number of bands, q and rho, and has no
pending-degree, active-slot, position-count or band-exponent loss. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators

/-- Genuine full-state ghost energy bound, with both concrete Schur rows
and the factorial transpose discharged by their actual arithmetic proofs. -/
theorem marked_minor_actual_raw_ghost_energy
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) {q ρ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hρ : 0 < ρ) (hgap : Real.sqrt q < ρ^2) :
    ∀ᶠ x : ℝ in atTop, ∀ (qStage : ℝ), 0 ≤ qStage → qStage ≤ Real.sqrt q →
      ∀ (M B : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
        (f : MarkedRawState (markedRawActualPrimeBand e x) M B Z → ℂ),
      (∀ z a, MarkedRawMemorySymmetric (fun m => f (z, (a, m)))) →
      (∑ s, markedRawStateMass (markedRawActualPrimeAtom e q x) s *
        ‖markedRawGhostApply (markedRawActualPrimeAtom e q x)
          (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) qStage ρ hZ f s‖^2) ≤
      (Real.exp ((Fintype.card J : ℝ) * (2 * markedRawGhostSchurParameter q ρ / ρ)))^2 *
        ∑ s, markedRawStateMass (markedRawActualPrimeAtom e q x) s * ‖f s‖^2 := by
  classical
  have hV := eventually_all.mpr (fun j => marked_log_power_band_mass_eventually
    (show 0 < e j by linarith [he j]))
  filter_upwards [markedRawGhostApply_actual_energy_le_reverse_eventually e he hq₀ hq₁ hρ hgap,
    markedRawGhostSwapped_actual_weighted_row_eventually e he hq₀ hq₁ hρ hgap,
    marked_actual_tilted_atom_comparison_eventually e he, hV] with x hc hr hν hV
  intro qStage hqs₀ hqs M B Z hZ f hf
  let C := Real.exp ((Fintype.card J : ℝ) * (2 * markedRawGhostSchurParameter q ρ / ρ))
  have hC : 0 ≤ C := (Real.exp_pos _).le
  have hνpos : ∀ j p, 0 ≤ markedRawActualPrimeAtom e q x j p := by
    intro j p
    rw [markedRawActualPrimeAtom_eq_tilted]
    exact (hν q hq₀ hq₁ j _).1
  have hVp : ∀ j, 0 ≤ bandReciprocalMass (markedLogPowerBand (e j) x) :=
    fun j => ((by positivity : 0 < Real.log 2/2).trans (hV j).1).le
  have hsqrt : Real.sqrt q ≤ 1 := by
    nlinarith [Real.sq_sqrt hq₀, Real.sqrt_nonneg q]
  have hv₀ : 0 < markedRawGhostSchurParameter q ρ :=
    (by norm_num : (0:ℝ)<1).trans_le (markedRawGhostSchurParameter_ge_one q ρ)
  have heq := markedRawGhostChoiceReverseEnergy_sum_eq_swapped_row
    (markedRawActualPrimeAtom e q x) hνpos
    (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hVp
    hqs₀ (hqs.trans hsqrt) hρ hv₀ hZ f hf
  calc
    _ ≤ C * ∑ s, markedRawStateMass (markedRawActualPrimeAtom e q x) s *
        markedRawGhostChoiceReverseEnergy (markedRawActualPrimeAtom e q x)
          (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) qStage ρ
          (markedRawGhostSchurParameter q ρ) hZ f s := hc qStage hqs₀ hqs M B Z hZ f
    _ = C * ∑ s, markedRawStateMass (markedRawActualPrimeAtom e q x) s * ‖f s‖^2 *
        markedRawGhostSwappedWeightedAbsRow (markedRawActualPrimeAtom e q x)
          (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) qStage ρ
          (markedRawGhostSchurParameter q ρ) s.2.2 s.1.1 (hZ _ s.1.2) := by rw [heq]
    _ ≤ C * (C * ∑ s, markedRawStateMass (markedRawActualPrimeAtom e q x) s * ‖f s‖^2) := by
      apply mul_le_mul_of_nonneg_left _ hC
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro s _
      calc
        _ ≤ markedRawStateMass (markedRawActualPrimeAtom e q x) s * ‖f s‖^2 * C :=
          mul_le_mul_of_nonneg_left (hr qStage hqs₀ hqs B s.2.2 s.1.1 (hZ _ s.1.2))
            (mul_nonneg (markedRawStateMass_nonneg _ hνpos s) (sq_nonneg _))
        _ = _ := by ring
    _ = _ := by change C * (C * _) = C^2 * _; ring

end
end ArtinMatthews
