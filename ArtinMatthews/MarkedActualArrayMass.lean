module

public import ArtinMatthews.MarkedArrayReciprocalBounds
public import ArtinMatthews.MarkedEstimateActualModel


set_option backward.privateInPublic true
@[expose] public section

/-! Actual uniform represented reciprocal masses for the prescribed
closed prime bands, including repeated-array collisions. -/

namespace ArtinMatthews

open Filter
open scoped BigOperators

noncomputable def markedArrayReciprocalConstant (K : ℕ) : ℝ :=
  (max 1 (1 / (Real.log 2 / 2) + 1 / 4)) ^ K

theorem markedArrayReciprocalConstant_pos (K : ℕ) : 0 < markedArrayReciprocalConstant K := by
  unfold markedArrayReciprocalConstant
  positivity

/-- Distinct actual band exponents give a bounded normalized reciprocal
coefficient mass. The bound depends only on their number. -/
theorem marked_actual_array_reciprocal_mass_eventually {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (he : ∀ i, 0 < e i) (hinj : Function.Injective e)
    (a : ι → ℕ) (ha : ∀ i, a i = 1 ∨ a i = 2) :
    ∀ᶠ x : ℝ in atTop,
      (∑ t ∈ representedArrayChoices (fun i => markedLogPowerBand (e i) x) a,
        |representedArrayCoefficient
          (fun i => bandReciprocalMass (markedLogPowerBand (e i) x)) a t| /
          (∏ p ∈ representedArraySelected t, p : ℕ)) ≤
        markedArrayReciprocalConstant (Fintype.card ι) := by
  have hm : ∀ᶠ x : ℝ in atTop, ∀ i,
      Real.log 2 / 2 < bandReciprocalMass (markedLogPowerBand (e i) x) ∧
        bandReciprocalMass (markedLogPowerBand (e i) x) < 1 :=
    eventually_all.mpr (fun i => marked_log_power_band_mass_eventually (he i))
  filter_upwards [marked_array_disjoint_eventually e hinj, hm] with x hd hm
  exact represented_array_reciprocal_mass_uniform _ a ha hd
    (by positivity : 0 < Real.log 2 / 2) (fun i => (hm i).1.le)

end ArtinMatthews
