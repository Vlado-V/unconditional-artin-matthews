module

public import ArtinMatthews.GiantMarkedResidual
public import ArtinMatthews.GiantPrimeInvariance
public import ArtinMatthews.MarkedArrayCoefficientMass
public import ArtinMatthews.MarkedProgressionGrowth


set_option backward.privateInPublic true
@[expose] public section

/-! Exact identification and structural bounds for the manuscript's actual
giant-prime window; all bounds are discharged using finite arithmetic and Mertens. -/

namespace ArtinMatthews

open Filter
open scoped BigOperators

theorem giantWindowDivisorCount_eq_card_filter (G : Finset ℕ) (u : ℕ) :
    giantWindowDivisorCount G u = ((G.filter (fun ell => ell ∣ u)).card : ℝ) := by
  classical
  simp [giantWindowDivisorCount]

theorem giantWindowDivisorCount_eq_actual {u : ℕ} (hu : u ≠ 0)
    {x ε : ℝ} (hx : 0 ≤ x) :
    giantWindowDivisorCount (giantPrimeWindow x ε) u = (giantPrimeFactors u x ε).card := by
  rw [giantPrimeFactors_eq_window_filter hu hx, giantWindowDivisorCount_eq_card_filter]

/-- The zero argument contributes nothing for a test vanishing at zero. -/
theorem giantWindowDivisorCount_test_eq_actual (Φ : ℝ → ℝ) (hΦzero : Φ 0 = 0)
    (H : ℕ → ℝ) {x ε : ℝ} (hx : 0 ≤ x) (u : ℕ) :
    Φ ((u : ℝ) / x) * (giantWindowDivisorCount (giantPrimeWindow x ε) u * H u) =
      Φ ((u : ℝ) / x) * ((giantPrimeFactors u x ε).card * H u) := by
  by_cases hu : u = 0
  · subst u
    simp only [Nat.cast_zero, zero_div, hΦzero, zero_mul]
  · rw [giantWindowDivisorCount_eq_actual hu hx]

/-- Actual giant-window hypotheses needed by the finite progression bound.
The finite marking family may have any fixed exponents less than one. -/
theorem giant_window_structure_eventually {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (he : ∀ i, e i < 1) {α ε : ℝ}
    (hα : α < 1) (hε : 0 < ε) (hεq : ε < 1 / 4) :
    ∀ᶠ x : ℝ in atTop,
      (∀ ell ∈ giantPrimeWindow x ε, ell.Prime) ∧
      Disjoint (giantPrimeWindow x ε) (Finset.univ.biUnion (fun i => markedLogPowerBand (e i) x)) ∧
      (∀ ell ∈ giantPrimeWindow x ε, Real.exp ((Real.log x) ^ α) ≤ (ell : ℝ)) ∧
      ((giantPrimeWindow x ε).card : ℝ) ≤ x ^ (1 - ε / 2) ∧
      (∑ ell ∈ giantPrimeWindow x ε, 1 / (ell : ℝ)) ≤ 1 := by
  classical
  have hband := eventually_all.mpr (fun i =>
    marked_band_below_giant_eventually (he i) (by linarith : ε < 1))
  have hlo := marked_sublinear_log_exp_le_rpow_eventually α 1 (1 - ε) hα (by linarith)
  filter_upwards [hband, hlo, giantPrimeReciprocalSum_bounds_eventually hε hεq,
    eventually_gt_atTop (1 : ℝ)] with x hb hl hmass hx
  have hx0 : 0 ≤ x := by linarith
  have hprime (ell : ℕ) (hell : ell ∈ giantPrimeWindow x ε) : ell.Prime :=
    (mem_giantPrimeWindow hx0).mp hell |>.1
  refine ⟨hprime, ?_, ?_, ?_, hmass.2⟩
  · apply Finset.disjoint_left.mpr
    intro ell hell hp
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    have hg := (mem_giantPrimeWindow hx0).mp hell |>.2.1
    exact (not_lt_of_ge (hb i ell hi)) hg
  · intro ell hell
    have hg := (mem_giantPrimeWindow hx0).mp hell |>.2.1
    simpa only [one_mul] using hl.trans hg.le
  · exact marked_prime_set_card_le _ hprime (Real.rpow_nonneg hx0 _)
      (fun ell hell => (mem_giantPrimeWindow hx0).mp hell |>.2.2)

end ArtinMatthews
