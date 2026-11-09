module

public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeActual
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeWeight


set_option backward.privateInPublic true
@[expose] public section

/-! The actual v0-weighted delta row retains the same explicit epsilon,
with only the fixed v0^K factor. -/
noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators Topology

set_option backward.isDefEq.respectTransparency false in
theorem markedDirtyRawEdge_actual_delta_weighted_row_eventually {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) (hinj : Function.Injective e)
    (I : Finset J) (jstar : J) (hstar : jstar ∈ I) :
    ∀ᶠ x : ℝ in atTop, ∀ (pads B : ℕ) (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ η : ℝ → ℂ) (d₀ Y q ρ H W v₀ : ℝ)
      (χ : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ)
      (s : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z) (w : ℤ × ℤ) (r : ℝ) (Q : Finset ℤ),
      1 ≤ v₀ → 1 ≤ B → 0 ≤ q → q ≤ 1 → 0 ≤ ρ → ρ < 1 → 0 ≤ H → 0 ≤ W →
      (∀ t, ‖η t‖ ≤ H) → (∀ t, ‖ψ t‖ ≤ W) → (∀ s, ‖χ s‖ ≤ 1) →
      (∀ j, Function.Injective (s.2.1 j)) → markedMinorIntegerDet s.1.1 w=1 →
      markedMinorIntegerTau r s.1.1 ≠ 0 →
      (∀ v ∈ Z, |markedMinorIntegerTau r v/markedMinorIntegerTau r s.1.1| ≤ 16) →
      markedDirtyRawEdgeTrials s.2.1 s.2.2 (I.erase jstar) ⊆ Q →
      ((markedMinorIntegerTau r w/markedMinorIntegerTau r s.1.1:ℝ):AddCircle (1:ℝ)) ∉
        {a | Real.exp (-((Real.log x)^(e jstar))/4) ≤
          markedPairFailureProbability Q
            (markedFreshIntegerProduct (fun j : ↥(Finset.univ \ I) => e j.1) x)
            (markedFreshHarmonicLaw (fun j : ↥(Finset.univ \ I) => e j.1) x)
            (100*Real.exp (-((Real.log x)^(e jstar)))) a} →
      markedDirtyRawEdgeDeltaWeightedRow (markedRawActualPrimeAtom e q x)
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hZ ψ η d₀ Y ρ v₀ χ s I ≤
        (v₀^(Fintype.card J)*markedDirtyActualRowConstant (Fintype.card J) ρ H W)*
          ((B:ℝ)*(pads+1:ℝ)⁻¹^(Fintype.card J)+(B:ℝ)^(Fintype.card J)*
            Real.exp (-((Real.log x)^(1/10:ℝ))/4)) := by
  classical
  have hV : ∀ᶠ x : ℝ in atTop, ∀ j, 0 < bandReciprocalMass (markedLogPowerBand (e j) x) :=
    eventually_all.mpr (fun j => (marked_log_power_band_mass_eventually (show 0 < e j by linarith [he j])).mono
      (fun _ hx => (by positivity : (0:ℝ)<Real.log 2/2).trans hx.1))
  filter_upwards [markedDirtyRawEdge_actual_delta_row_eventually e he hinj I jstar hstar,
    marked_actual_tilted_atom_comparison_eventually e he,hV] with x hrow hνx hV
  intro pads B Z hZ ψ η d₀ Y q ρ H W v₀ χ s w r Q hv₀ hB hq0 hq1 hρ0 hρ1 hH hW hη hψ hχ
    hdist hd hz hbox hQ hroot
  have hν : ∀ j p, 0 ≤ markedRawActualPrimeAtom e q x j p := by
    intro j p
    rw [markedRawActualPrimeAtom_eq_tilted]
    exact (hνx q hq0 hq1 j _).1
  have hw := markedDirtyRawEdge_delta_weighted_row_le (markedRawActualPrimeAtom e q x)
    (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hν hV hZ ψ η d₀ Y ρ v₀ hv₀ χ s I
  have hr := hrow pads B Z hZ ψ η d₀ Y q ρ H W χ s w r Q hB hq0 hq1 hρ0 hρ1 hH hW hη hψ hχ
    hdist hd hz hbox hQ hroot
  exact (hw.trans (mul_le_mul_of_nonneg_left hr (pow_nonneg (by linarith) _))).trans_eq (by ring)

end ArtinMatthews
