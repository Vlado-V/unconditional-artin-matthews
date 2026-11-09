module

public import ArtinMatthews.GiantCandidateFirstEndpoint
public import ArtinMatthews.GiantWindowArithmetic


set_option backward.privateInPublic true
@[expose] public section

/-! The bounded extension of the actual giant statistic agrees with the
giant divisor count on the larger comparison scale. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators Topology
noncomputable section

theorem boundedGiantIndicator_eq_card_of_threshold_square {n : ℕ} {x ε : ℝ}
    (hn : 0 < n) (hx : 0 ≤ x) (hnx : (n : ℝ) ≤ (x ^ (1 - ε)) ^ 2) :
    boundedGiantIndicator n x ε = (giantPrimeFactors n x ε).card := by
  classical
  have hc : (giantPrimeFactors n x ε).card ≤ 1 := by
    apply card_le_one.mpr
    intro p hp q hq
    by_contra hne
    simp only [giantPrimeFactors, mem_filter, mem_primeFactorsAbove] at hp hq
    obtain ⟨⟨hp, hpn, _, hpl⟩, _⟩ := hp
    obtain ⟨⟨hq, hqn, _, hql⟩, _⟩ := hq
    have hcop := (Nat.coprime_primes hp hq).mpr hne
    have hprod : p * q ∣ n := hcop.mul_dvd_of_dvd_of_dvd hpn hqn
    have hle : (p : ℝ) * q ≤ n := by exact_mod_cast Nat.le_of_dvd hn hprod
    have hq₀ : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have hlt : (x ^ (1 - ε)) ^ 2 < (p : ℝ) * q := by
      rw [pow_two]
      exact (mul_le_mul_of_nonneg_left hql.le (Real.rpow_nonneg hx _)).trans_lt
        (mul_lt_mul_of_pos_right hpl hq₀)
    exact (not_lt_of_ge (hle.trans hnx)) hlt
  unfold boundedGiantIndicator
  by_cases h : (giantPrimeFactors n x ε).Nonempty
  · have hc' := card_pos.mpr h
    have he : (giantPrimeFactors n x ε).card = 1 := by omega
    simp [h, he]
  · have he : giantPrimeFactors n x ε = ∅ := not_nonempty_iff_eq_empty.mp h
    simp [he]

theorem sourceComparisonGiantCenter_eq_window {n : ℕ} {x ε : ℝ}
    (hn : 0 < n) (hx : 0 ≤ x) (hnx : (n : ℝ) ≤ (x ^ (1 - ε)) ^ 2) :
    giantMarkedCenteredCore ε x n =
      (giantWindowDivisorCount (giantPrimeWindow x ε) n -
        ∑ p ∈ giantPrimeWindow x ε, 1 / (p : ℝ) : ℝ) := by
  unfold giantMarkedCenteredCore
  rw [boundedGiantIndicator_eq_card_of_threshold_square hn hx hnx,
    ← giantWindowDivisorCount_eq_actual hn.ne' hx]
  rfl

theorem sourceComparisonGiantCenter_eq_window_eventually (B : ℝ) (hB : 0 ≤ B)
    {ε : ℝ} (hε : ε ≤ 1 / 4) :
    ∀ᶠ x : ℝ in atTop, ∀ Y : ℝ, Y ≤ x ^ (1 + ε / 4) →
      ∀ n : ℕ, 0 < n → (n : ℝ) ≤ B * Y →
        giantMarkedCenteredCore ε x n =
          (giantWindowDivisorCount (giantPrimeWindow x ε) n -
            ∑ p ∈ giantPrimeWindow x ε, 1 / (p : ℝ) : ℝ) := by
  have hg : 0 < 2 * (1 - ε) - (1 + ε / 4) := by linarith
  filter_upwards [(tendsto_rpow_atTop hg).eventually (eventually_ge_atTop B),
    eventually_gt_atTop (0 : ℝ)] with x hpow hx
  intro Y hY n hn hnY
  apply sourceComparisonGiantCenter_eq_window hn hx.le
  calc
    (n : ℝ) ≤ B * Y := hnY
    _ ≤ B * x ^ (1 + ε / 4) := mul_le_mul_of_nonneg_left hY hB
    _ ≤ x ^ (2 * (1 - ε) - (1 + ε / 4)) * x ^ (1 + ε / 4) :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hx.le _)
    _ = (x ^ (1 - ε)) ^ 2 := by
      rw [← Real.rpow_add hx, ← Real.rpow_two (x ^ (1 - ε)), ← Real.rpow_mul hx.le]
      congr 1
      ring

end
end ArtinMatthews
