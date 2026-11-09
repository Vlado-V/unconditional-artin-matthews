module

public import ArtinMatthews.GiantActualArrayProgressions
public import ArtinMatthews.MarkedActualMomentProgressions


set_option backward.privateInPublic true
@[expose] public section

/-! The actual giant-factor progression law with the exact independent
Bernoulli mean, ready for the two-sided positive sieve. -/

namespace ArtinMatthews

open Filter
open scoped BigOperators Asymptotics Topology

theorem giant_actual_first_moment_progressions {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → ℝ) (he : ∀ i, (1 / 10 : ℝ) < e i ∧ e i < 1 / 5)
    (hinj : Function.Injective e) (ε c A : ℝ)
    (hε : 0 < ε) (hεq : ε < 1 / 4) (hc0 : 0 ≤ c) (hc1 : c < ε / 2)
    (Φ : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hΦ : Differentiable ℝ Φ)
    (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0) (hΦ0 : ∀ t, 0 ≤ Φ t)
    (hΦzero : Φ 0 = 0) :
    (fun x : ℝ => markedProgressionDiscrepancy
      (fun u => (giantPrimeFactors u x ε).card *
        divisorWeight Finset.univ (fun i => markedLogPowerBand (e i) x)
          (fun i => bandReciprocalMass (markedLogPowerBand (e i) x)) u)
      (giantPrimeReciprocalSum x ε *
        independentArrayMean (fun i => markedLogPowerBand (e i) x)
          (fun i => bandReciprocalMass (markedLogPowerBand (e i) x))) Φ T x ⌊x ^ c⌋₊)
      =o[atTop] (fun x : ℝ => x * (Real.log x) ^ (-A)) := by
  have h := giant_actual_array_progression_isLittleO e he hinj (fun _ => 1)
    (fun _ => Or.inl rfl) ε c A hε hεq hc0 hc1 Φ hT hΦ hderiv hΦT hΦ0 hΦzero
  apply h.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [marked_array_disjoint_eventually e hinj] with x hd
  unfold giantActualArrayProgressionDiscrepancy markedProgressionDiscrepancy divisorWeight
  rw [representedArrayEulerMean_one _ (fun i p hp => (mem_markedLogPowerBand.mp hp).1) _ hd]
  simp only [pow_one]

end ArtinMatthews
