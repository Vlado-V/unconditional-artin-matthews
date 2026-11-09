module

public import ArtinMatthews.MarkedBirthHighRankBudget


set_option backward.privateInPublic true
@[expose] public section

/-! Summing every high-rank coefficient at the actual potential-address
cutoff. The auxiliary cutoff constant is fixed before x; the original
memory cap and moment length are not enlarged. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators

theorem markedBirth_rank_count_le_moment_power (K : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      (markedMemoryPotentialAddressCount K x+1:ℝ) ≤
        (Real.log x)^(markedMemoryMomentLength x) := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max 16 (16*(K:ℝ)+1)))] with x hx
  let L := Real.log x
  have hL16 : 16 ≤ L := (le_max_left _ _).trans hx
  have hLK : 16*(K:ℝ)+1 ≤ L := (le_max_right _ _).trans hx
  have hL₁ : 1 ≤ L := by linarith
  have hQ := markedMemoryPotentialAddressCount_polynomial K hL₁
  have hL₃ : 1 ≤ L^3 := one_le_pow₀ hL₁
  have hN : 4 ≤ markedMemoryMomentLength x := by
    have hs : (4:ℝ) ≤ L^(1/2:ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      exact (Real.le_sqrt (by norm_num) (by linarith)).mpr (by nlinarith)
    exact_mod_cast hs.trans (markedMemoryMomentLength_lower (by linarith))
  calc
    _ ≤ 16*(K:ℝ)*L^3+1 := by exact_mod_cast (show
      (markedMemoryPotentialAddressCount K x:ℝ)+1 ≤ 16*(K:ℝ)*L^3+1 by linarith)
    _ ≤ (16*(K:ℝ)+1)*L^3 := by nlinarith
    _ ≤ L*L^3 := mul_le_mul_of_nonneg_right hLK (pow_nonneg (by linarith) _)
    _ = L^4 := by ring
    _ ≤ _ := pow_le_pow_right₀ hL₁ hN

theorem markedBirth_high_rank_sum_budget (K : ℕ) (P G cutoffScale : ℝ)
    (hP : 0 ≤ P) (hScale : 2*(2*P+G+2) ≤ cutoffScale) :
    ∀ᶠ x : ℝ in atTop,
      (∑ r ∈ Finset.range (markedMemoryPotentialAddressCount K x+1),
        if markedBirthRankCutoff cutoffScale x ≤ r then
          ((markedMemoryPotentialAddressCount K x:ℝ)^2+1)^(2*r)*
            ((Real.log x)^P)^(markedMemoryMomentLength x+1)*
            (markedMemoryBirthAtomEnvelope x)^r else 0) ≤
      ((Real.log x)^(-(G+1)))^(markedMemoryMomentLength x) := by
  filter_upwards [markedBirth_high_rank_term_budget K P G cutoffScale hP hScale,
    markedBirth_rank_count_le_moment_power K,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hterm hcount hlog
  let L := Real.log x
  let N := markedMemoryMomentLength x
  have hL : 0 < L := zero_lt_one.trans_le hlog
  have htarget : 0 ≤ (L^(-(G+2)))^N := pow_nonneg (Real.rpow_nonneg hL.le _) _
  calc
    _ ≤ ∑ _r ∈ Finset.range (markedMemoryPotentialAddressCount K x+1), (L^(-(G+2)))^N := by
      apply Finset.sum_le_sum
      intro r _
      split_ifs with hr
      · exact hterm r hr
      · exact htarget
    _ = (markedMemoryPotentialAddressCount K x+1:ℝ)*(L^(-(G+2)))^N := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      norm_cast
    _ ≤ L^N*(L^(-(G+2)))^N := mul_le_mul_of_nonneg_right hcount htarget
    _ = (L^(-(G+1)))^N := by
      have hp : L*L^(-(G+2))=L^(-(G+1)) := by
        calc
          _ = L^(1:ℝ)*L^(-(G+2)) :=
            congrArg (fun t => t*L^(-(G+2))) (Real.rpow_one L).symm
          _ = _ := by rw [← Real.rpow_add hL]; congr 1; ring
      rw [← mul_pow,hp]

end ArtinMatthews
