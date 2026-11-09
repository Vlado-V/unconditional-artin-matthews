module

public import ArtinMatthews.MarkedEstimateActualModel


set_option backward.privateInPublic true
@[expose] public section

/-! The actual prime bands satisfy the structural endpoint, disjointness,
normalizer, and total reciprocal-mass hypotheses of the array progression
estimate. Mertens supplies the normalizers; no distribution assumption is used. -/

namespace ArtinMatthews

open Filter
open scoped BigOperators

/-- Endpoint comparison with common fixed lower and upper exponents. -/
theorem marked_band_common_endpoints {e α β x : ℝ}
    (hlog : 1 ≤ Real.log x) (hα : α ≤ e) (hβ : e ≤ β) {p : ℕ}
    (hp : p ∈ markedLogPowerBand e x) :
    p.Prime ∧ Real.exp ((Real.log x) ^ α) ≤ (p : ℝ) ∧
      (p : ℝ) ≤ Real.exp (2 * (Real.log x) ^ β) := by
  obtain ⟨hprime, hlo, hhi⟩ := mem_markedLogPowerBand.mp hp
  refine ⟨hprime, ?_, ?_⟩
  · exact (Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hlog hα)).trans hlo
  · exact hhi.trans (Real.exp_le_exp.mpr (by
      have h := Real.rpow_le_rpow_of_exponent_le hlog hβ
      linarith))

/-- All noncombinatorial structural hypotheses hold for the literal closed
prime bands, with common lower normalizer `log 2 / 2`. -/
theorem marked_actual_band_structure_eventually {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (he : ∀ i, 0 < e i) (hinj : Function.Injective e)
    {α β : ℝ} (hα : ∀ i, α ≤ e i) (hβ : ∀ i, e i ≤ β) :
    ∀ᶠ x : ℝ in atTop,
      Pairwise (fun i j => Disjoint (markedLogPowerBand (e i) x) (markedLogPowerBand (e j) x)) ∧
      (∀ i p, p ∈ markedLogPowerBand (e i) x →
        p.Prime ∧ Real.exp ((Real.log x) ^ α) ≤ (p : ℝ) ∧
          (p : ℝ) ≤ Real.exp (2 * (Real.log x) ^ β)) ∧
      (∀ i, Real.log 2 / 2 ≤ bandReciprocalMass (markedLogPowerBand (e i) x)) ∧
      (∑ p ∈ Finset.univ.biUnion (fun i => markedLogPowerBand (e i) x), 1 / (p : ℝ)) ≤
        Fintype.card ι := by
  classical
  have hm : ∀ᶠ x : ℝ in atTop, ∀ i,
      Real.log 2 / 2 < bandReciprocalMass (markedLogPowerBand (e i) x) ∧
        bandReciprocalMass (markedLogPowerBand (e i) x) < 1 :=
    eventually_all.mpr (fun i => marked_log_power_band_mass_eventually (he i))
  filter_upwards [marked_array_disjoint_eventually e hinj, hm,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with x hd hm hlog
  refine ⟨hd, (fun i p hp => marked_band_common_endpoints hlog (hα i) (hβ i) hp),
    (fun i => (hm i).1.le), ?_⟩
  rw [Finset.sum_biUnion (fun i _ j _ hij => hd hij)]
  change (∑ i, bandReciprocalMass (markedLogPowerBand (e i) x)) ≤ Fintype.card ι
  calc
    _ ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (hm i).2.le)
    _ = _ := by simp

end ArtinMatthews
