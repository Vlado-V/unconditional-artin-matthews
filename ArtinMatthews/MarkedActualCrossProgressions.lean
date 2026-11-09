module

public import ArtinMatthews.MarkedActualMomentProgressions


set_option backward.privateInPublic true
@[expose] public section

/-! The cross-array progression estimate. Distinct arrays use the full
product of first moments; repeated arrays use the separate second-moment
result, retaining all coincident represented selections. -/

namespace ArtinMatthews

open Filter
open scoped BigOperators Asymptotics Topology

theorem marked_actual_cross_moment_progressions {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι → ℝ) (f : κ → ℝ)
    (he : ∀ i, (1 / 10 : ℝ) < e i ∧ e i < 1 / 5)
    (hf : ∀ j, (1 / 10 : ℝ) < f j ∧ f j < 1 / 5)
    (hinj : Function.Injective (Sum.elim e f)) (c A : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (Φ : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hΦ : Differentiable ℝ Φ)
    (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0) (hΦ0 : ∀ t, 0 ≤ Φ t) :
    (fun x : ℝ => markedProgressionDiscrepancy
      (fun u => divisorWeight Finset.univ (fun i => markedLogPowerBand (e i) x)
          (fun i => bandReciprocalMass (markedLogPowerBand (e i) x)) u *
        divisorWeight Finset.univ (fun j => markedLogPowerBand (f j) x)
          (fun j => bandReciprocalMass (markedLogPowerBand (f j) x)) u)
      (independentArrayMean (fun i => markedLogPowerBand (e i) x)
          (fun i => bandReciprocalMass (markedLogPowerBand (e i) x)) *
        independentArrayMean (fun j => markedLogPowerBand (f j) x)
          (fun j => bandReciprocalMass (markedLogPowerBand (f j) x))) Φ T x ⌊x ^ c⌋₊) =o[atTop]
      (fun x : ℝ => x * (Real.log x) ^ (-A)) := by
  have hrange : ∀ z, (1 / 10 : ℝ) < Sum.elim e f z ∧ Sum.elim e f z < 1 / 5 := by
    intro z
    cases z with
    | inl i => exact he i
    | inr j => exact hf j
  have h := marked_actual_first_moment_progressions (Sum.elim e f) hrange hinj c A hc0 hc1
    Φ hT hΦ hderiv hΦT hΦ0
  simpa only [markedProgressionDiscrepancy, divisorWeight, independentArrayMean_eq, Fintype.prod_sum_type,
    Sum.elim_inl, Sum.elim_inr] using h

end ArtinMatthews
