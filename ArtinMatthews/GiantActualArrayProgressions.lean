module

public import ArtinMatthews.GiantActualArrayWindow


set_option backward.privateInPublic true
@[expose] public section

/-! The actual giant-prime statistic in the all-logarithmic progression law.
This is the ordinary-modulus (M=1) marked giant-factor input of (3.6). -/

namespace ArtinMatthews

open Filter MeasureTheory
open scoped BigOperators Asymptotics Topology

noncomputable def giantActualArrayProgressionDiscrepancy {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (W : ι → ℝ) (a : ι → ℕ) (ε : ℝ) (Φ : ℝ → ℝ)
    (T x : ℝ) (R : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 R,
    |(∑ u ∈ (Finset.Icc 0 ⌊T * x⌋₊).filter (fun u => r ∣ u + 1),
        Φ ((u : ℝ) / x) * ((giantPrimeFactors u x ε).card *
          ∏ i, (bandWeight (P i) (W i) u) ^ a i)) -
      ((x * ∫ t in Set.Ioc 0 T, Φ t) / (r : ℝ)) *
        (giantPrimeReciprocalSum x ε * representedArrayEulerMean P W a)|

theorem giant_window_discrepancy_eq_actual {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (W : ι → ℝ) (a : ι → ℕ) (ε : ℝ) (Φ : ℝ → ℝ)
    (hΦzero : Φ 0 = 0) (T x : ℝ) (hx : 0 ≤ x) (R : ℕ) :
    giantMarkedArrayProgressionDiscrepancy (giantPrimeWindow x ε) P W a Φ T x R =
      giantActualArrayProgressionDiscrepancy P W a ε Φ T x R := by
  unfold giantMarkedArrayProgressionDiscrepancy giantActualArrayProgressionDiscrepancy
  simp_rw [giantWindowDivisorCount_test_eq_actual Φ hΦzero
    (fun u => ∏ i, (bandWeight (P i) (W i) u) ^ a i) hx]
  rfl

/-- Full all-logarithmic saving for the literal giant statistic and literal
marking arrays, including repeated-array moments. No analytic estimate is
assumed; the independent Euler mean and C_x are the actual finite quantities. -/
theorem giant_actual_array_progression_isLittleO {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (he : ∀ i, (1 / 10 : ℝ) < e i ∧ e i < 1 / 5)
    (hinj : Function.Injective e) (a : ι → ℕ) (ha : ∀ i, a i = 1 ∨ a i = 2)
    (ε c A : ℝ) (hε : 0 < ε) (hεq : ε < 1 / 4) (hc0 : 0 ≤ c) (hc1 : c < ε / 2)
    (Φ : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hΦ : Differentiable ℝ Φ)
    (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0) (hΦ0 : ∀ t, 0 ≤ Φ t)
    (hΦzero : Φ 0 = 0) :
    (fun x : ℝ => giantActualArrayProgressionDiscrepancy
      (fun i => markedLogPowerBand (e i) x)
      (fun i => bandReciprocalMass (markedLogPowerBand (e i) x)) a ε Φ T x ⌊x ^ c⌋₊)
      =o[atTop] (fun x : ℝ => x * (Real.log x) ^ (-A)) := by
  have h := giant_actual_array_window_progression_isLittleO e he hinj a ha ε c A
    hε hεq hc0 hc1 Φ hT hΦ hderiv hΦT hΦ0
  apply h.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  exact giant_window_discrepancy_eq_actual _ _ a ε Φ hΦzero T x hx _

end ArtinMatthews
