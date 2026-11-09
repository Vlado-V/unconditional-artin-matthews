module

public import ArtinMatthews.MarkedMinorArcDirtyFreshGood


set_option backward.privateInPublic true
@[expose] public section

/-! Actual fresh tilted tuples have bounded total mass; no probability
normalization is imposed on their unnormalized tilted law. -/
noncomputable section
namespace ArtinMatthews

open Filter
open scoped BigOperators Topology

theorem markedFreshTiltedLaw_mass_eventually {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      (∀ t, 0 ≤ markedFreshTiltedLaw e q x t) ∧
        (∑ t, markedFreshTiltedLaw e q x t) ≤ (2:ℝ)^(Fintype.card J) := by
  classical
  filter_upwards [marked_actual_tilted_atom_comparison_eventually e he,
    marked_actual_harmonic_fresh_probability_eventually e (fun j => by linarith [he j])] with x hc hμ
  intro q hq0 hq1
  refine ⟨fun t => Finset.prod_nonneg (fun j _ => (hc q hq0 hq1 j (t j)).1),?_⟩
  have hh := marked_fresh_event_mass_comparison
    (fun j => markedTiltedBandAtom (markedLogPowerBand (e j) x) q (markedMemoryMomentLength x))
    (fun j => markedHarmonicAtom (markedLogPowerBand (e j) x))
    (fun j p => (hc q hq0 hq1 j p).1) (fun j p => (hc q hq0 hq1 j p).2) (fun _ => True)
  simp only [markedEventMass,ite_true,one_mul] at hh
  change (∑ t, markedFreshTiltedLaw e q x t) ≤
    (2:ℝ)^(Fintype.card J)*(∑ t, markedFreshHarmonicLaw e x t) at hh
  simpa only [hμ.2,mul_one] using hh

end ArtinMatthews
