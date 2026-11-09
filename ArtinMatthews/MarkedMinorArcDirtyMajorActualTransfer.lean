module

public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeActualFresh
public import ArtinMatthews.MarkedMinorArcDirtyRowFreshMass


set_option backward.privateInPublic true
@[expose] public section

/-! Literal log-band prime integrations and reciprocal normalizers for the
actual major edge row. -/
noncomputable section
namespace ArtinMatthews

open Filter
open scoped BigOperators Topology

theorem markedDirty_transfer_constant_one_le : (1:ℝ) ≤ 2/Real.log 2 := by
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]

theorem markedDirty_actual_band_transfer_eventually {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      (∀ j p, 0 ≤ markedRawActualPrimeAtom e q x j p) ∧
      (∀ j, 0 < bandReciprocalMass (markedLogPowerBand (e j) x) ∧
        (bandReciprocalMass (markedLogPowerBand (e j) x))⁻¹ ≤ 2/Real.log 2) ∧
      (∑ fresh : (j : J) → ↥(markedRawActualPrimeBand e x j),
        finiteProductMass (markedRawActualPrimeAtom e q x) fresh) ≤ (2:ℝ)^(Fintype.card J) := by
  classical
  have hV : ∀ᶠ x : ℝ in atTop, ∀ j, Real.log 2/2 ≤ bandReciprocalMass (markedLogPowerBand (e j) x) :=
    eventually_all.mpr (fun j => (marked_log_power_band_mass_eventually (show 0 < e j by linarith [he j])).mono
      (fun _ hx => hx.1.le))
  filter_upwards [hV,marked_actual_tilted_atom_comparison_eventually e he,
    markedFreshTiltedLaw_mass_eventually e he] with x hV hν hm
  intro q hq0 hq1
  refine ⟨?_,?_,?_⟩
  · intro j p
    rw [markedRawActualPrimeAtom_eq_tilted]
    exact (hν q hq0 hq1 j _).1
  · intro j
    have hp : 0 < Real.log 2/2 := by positivity
    refine ⟨hp.trans_le (hV j),?_⟩
    calc
      _ = 1/bandReciprocalMass (markedLogPowerBand (e j) x) := (one_div _).symm
      _ ≤ 1/(Real.log 2/2) := one_div_le_one_div_of_le hp (hV j)
      _ = _ := by rw [div_div_eq_mul_div]; ring
  · have hs := markedDirtyActualFresh_expectation_eq e q x (fun _ => (1:ℝ))
    simp only [mul_one] at hs
    exact hs.le.trans (hm q hq0 hq1).2

end ArtinMatthews
