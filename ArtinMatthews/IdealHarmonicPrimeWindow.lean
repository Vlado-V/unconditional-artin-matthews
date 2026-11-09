module

public import ArtinMatthews.IdealHarmonicDyadicPartition


set_option backward.privateInPublic true
@[expose] public section

/-! Reciprocal-prime cancellation over arbitrary sharp windows, derived
from the actual dyadic Siegel--Walfisz theorem. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealHarmonicPrime_window (a P : ℝ) (ha : 0 ≤ a) (hP : 0 ≤ P) :
    ∃ C H₀ : ℝ, 0 < C ∧ 2 ≤ H₀ ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (u v : ℝ),
        2*H₀ ≤ u → u ≤ v → (q : ℝ) ≤ (Real.log (u/2))^a → χ ≠ 1 →
        ‖idealHarmonicPrimeInterval χ u v‖ ≤
          C*(1 + Real.log (v+1)/Real.log 2)*(Real.log (u/2))^(-P) := by
  obtain ⟨C, hC, hdyad⟩ := idealHarmonicPrime_dyad a P ha hP
  obtain ⟨H₀, hH₀⟩ := eventually_atTop.mp (hdyad.and (eventually_ge_atTop (2 : ℝ)))
  refine ⟨C, max H₀ 2, hC, le_max_right _ _, ?_⟩
  intro q _ χ u v hu huv hq hχ
  have hu4 : 4 ≤ u := by have := le_max_right H₀ (2 : ℝ); linarith
  have hu0 : 0 ≤ u := by linarith
  have hv0 : 0 ≤ v := hu0.trans huv
  have hu2 : 0 < u/2 := by linarith
  have hlog : 0 < Real.log (u/2) := Real.log_pos (by linarith)
  have hbound (k : ℕ) :
      ‖idealHarmonicPrimeInterval χ (max u ((2 : ℝ)^k)) (min v (2*(2 : ℝ)^k))‖ ≤
        C*(Real.log (u/2))^(-P) := by
    by_cases hnonempty : max u ((2 : ℝ)^k) ≤ min v (2*(2 : ℝ)^k)
    · have hscale : u/2 ≤ (2 : ℝ)^k := by
        have hleft := le_max_left u ((2 : ℝ)^k)
        have hright := min_le_right v (2*(2 : ℝ)^k)
        linarith
      have hbase : H₀ ≤ (2 : ℝ)^k := by
        have hmax := le_max_left H₀ (2 : ℝ)
        linarith
      obtain ⟨htest, _⟩ := hH₀ ((2 : ℝ)^k) hbase
      have hlogs : Real.log (u/2) ≤ Real.log ((2 : ℝ)^k) :=
        Real.log_le_log hu2 hscale
      have hq' : (q : ℝ) ≤ (Real.log ((2 : ℝ)^k))^a :=
        hq.trans (Real.rpow_le_rpow hlog.le hlogs ha)
      have hh := htest q χ (max u ((2 : ℝ)^k)) (min v (2*(2 : ℝ)^k))
        hq' hχ (le_max_right _ _) hnonempty (min_le_right _ _)
      exact hh.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hlog hlogs (neg_nonpos.mpr hP)) hC.le)
    · have hempty : Ioc ⌊max u ((2 : ℝ)^k)⌋₊ ⌊min v (2*(2 : ℝ)^k)⌋₊ = ∅ :=
        Ioc_eq_empty (not_lt.mpr (Nat.floor_mono (not_le.mp hnonempty).le))
      simp only [idealHarmonicPrimeInterval, hempty, filter_empty, sum_empty, norm_zero]
      positivity
  rw [idealHarmonicPrimeInterval_dyadic χ u v hu0 hv0]
  calc
    _ ≤ ∑ k ∈ range (Nat.log 2 ⌊v⌋₊ + 1),
        ‖idealHarmonicPrimeInterval χ (max u ((2 : ℝ)^k)) (min v (2*(2 : ℝ)^k))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _k ∈ range (Nat.log 2 ⌊v⌋₊ + 1), C*(Real.log (u/2))^(-P) :=
      sum_le_sum fun k _ => hbound k
    _ = ((Nat.log 2 ⌊v⌋₊ + 1 : ℕ) : ℝ) * (C*(Real.log (u/2))^(-P)) := by
      rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ (1 + Real.log (v+1)/Real.log 2) * (C*(Real.log (u/2))^(-P)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      calc
        _ ≤ 1 + Real.log ((⌊v⌋₊ : ℝ)+1)/Real.log 2 := by
          simpa only [Nat.cast_add, Nat.cast_one] using primeExtractionDyadicIndex_count_le ⌊v⌋₊
        _ ≤ _ := by
          have hl : Real.log ((⌊v⌋₊ : ℝ)+1) ≤ Real.log (v+1) :=
            Real.log_le_log (by positivity) (by have := Nat.floor_le hv0; linarith)
          have hd := div_le_div_of_nonneg_right hl (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
          linarith
    _ = _ := by ring

end
end ArtinMatthews
