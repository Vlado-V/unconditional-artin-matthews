module

public import ArtinMatthews.MarkedBirthRankCoefficientBudget
public import ArtinMatthews.MarkedBirthMixedBudget


set_option backward.privateInPublic true
@[expose] public section

/-! The actual low-rank numerical sum. The coarser proved coefficient
count is absorbed with the existing two-power signed-edge margin, for
every fixed K and every fixed crude exponent. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators

theorem markedBirth_low_rank_budget (K : ℕ) (C P G cutoffScale : ℝ)
    (hC : 1 ≤ C) (hP : 0 ≤ P) (hG : 0 < G) (hScale : 0 ≤ cutoffScale) :
    ∀ᶠ x : ℝ in atTop,
      (∑ r ∈ Finset.range (markedBirthRankCutoff cutoffScale x),
        ((markedMemoryPotentialAddressCount K x:ℝ)^2+1)^(2*r) * 2*C^(markedMemoryMomentLength x+1) *
          ((Real.log x)^(-(G+2)))^(markedMemoryMomentLength x-2*r) *
          ((Real.log x)^P)^(2*r)) ≤
      ((Real.log x)^(-(G+1)))^(markedMemoryMomentLength x) := by
  let D := 2*(G+2)+2*P+13
  have hD₁ : 1 ≤ D := by dsimp [D]; linarith
  have hD : 0 < D := zero_lt_one.trans_le hD₁
  have hη : 0 < 1/(2*D) := by positivity
  filter_upwards [markedBirthRankCoefficientBase_polynomial K,
    markedBirthRank_boundary_prefactor_eventually hC,
    markedBirthRankCutoff_le_fraction hScale hη,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hcoeff hpref hcut hlog
  let L := Real.log x
  let N := markedMemoryMomentLength x
  let r₀ := markedBirthRankCutoff cutoffScale x
  have hL₁ : 1 ≤ L := hlog
  have hL : 0 < L := zero_lt_one.trans_le hL₁
  have hDcut : D*(r₀:ℝ) ≤ (N:ℝ)/2 := by
    calc
      _ ≤ D*((1/(2*D))*(N:ℝ)) := mul_le_mul_of_nonneg_left hcut hD.le
      _ = _ := by field_simp
  have hr₀N : (r₀:ℝ) ≤ (N:ℝ) := by
    have hrle : (r₀:ℝ) ≤ D*(r₀:ℝ) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hD₁ (show (0:ℝ) ≤ (r₀:ℝ) from Nat.cast_nonneg _)
    linarith
  let Z := L^(-(G+2)*(N:ℝ)+(N:ℝ)/2)
  have hZ : 0 ≤ Z := Real.rpow_nonneg hL.le _
  have hC₀ : 0 ≤ C := zero_le_one.trans hC
  have hterm (r : ℕ) (hr : r ∈ Finset.range r₀) :
      ((markedMemoryPotentialAddressCount K x:ℝ)^2+1)^(2*r)*2*C^(N+1)*
        (L^(-(G+2)))^(N-2*r)*(L^P)^(2*r) ≤ 2*C^(N+1)*Z := by
    have hrr : (r:ℝ) ≤ (r₀:ℝ) := by exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hr))
    have hrD : D*(r:ℝ) ≤ (N:ℝ)/2 := (mul_le_mul_of_nonneg_left hrr hD.le).trans hDcut
    have hrle : (r:ℝ) ≤ D*(r:ℝ) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hD₁ (show (0:ℝ) ≤ (r:ℝ) from Nat.cast_nonneg _)
    have h2r : 2*r ≤ N := by exact_mod_cast (show 2*(r:ℝ) ≤ (N:ℝ) by linarith)
    have hcoef : ((markedMemoryPotentialAddressCount K x:ℝ)^2+1)^(2*r) ≤ (L^13)^r := by
      rw [pow_mul]
      exact pow_le_pow_left₀ (sq_nonneg _) hcoeff r
    have h13 : (L^13)^r = L^(13*(r:ℝ)) := by
      rw [← Real.rpow_natCast L 13,← Real.rpow_mul_natCast hL.le]
      norm_num
    have he : (L^(-(G+2)))^(N-2*r) = L^(-(G+2)*((N-2*r:ℕ):ℝ)) := by
      rw [← Real.rpow_mul_natCast hL.le]
    have hpp : (L^P)^(2*r) = L^(P*((2*r:ℕ):ℝ)) := by rw [← Real.rpow_mul_natCast hL.le]
    have hpow : L^(13*(r:ℝ))*L^(-(G+2)*((N-2*r:ℕ):ℝ))*L^(P*((2*r:ℕ):ℝ)) =
        L^(-(G+2)*(N:ℝ)+D*(r:ℝ)) := by
      rw [← Real.rpow_add hL,← Real.rpow_add hL]
      congr 1
      simp only [Nat.cast_sub h2r,Nat.cast_mul,Nat.cast_ofNat]
      dsimp [D]
      ring
    calc
      _ ≤ (L^13)^r*2*C^(N+1)*(L^(-(G+2)))^(N-2*r)*(L^P)^(2*r) := by
        gcongr
      _ = 2*C^(N+1)*L^(-(G+2)*(N:ℝ)+D*(r:ℝ)) := by
        rw [h13,he,hpp]
        calc
          _ = 2*C^(N+1)*(L^(13*(r:ℝ))*L^(-(G+2)*((N-2*r:ℕ):ℝ))*L^(P*((2*r:ℕ):ℝ))) := by ring
          _ = _ := by rw [hpow]
      _ ≤ 2*C^(N+1)*Z := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL₁ (by linarith)) (by positivity)
  calc
    _ ≤ ∑ _r ∈ Finset.range r₀, 2*C^(N+1)*Z := Finset.sum_le_sum hterm
    _ = (r₀:ℝ)*(2*C^(N+1)*Z) := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    _ ≤ (N:ℝ)*(2*C^(N+1)*Z) := mul_le_mul_of_nonneg_right hr₀N (by positivity)
    _ = (2*(N:ℝ)*C^(N+1))*Z := by ring
    _ ≤ ((L^(1/2:ℝ))^N)*Z := mul_le_mul_of_nonneg_right hpref hZ
    _ = (L^(-(G+1)))^N := by
      dsimp [Z]
      rw [← Real.rpow_mul_natCast hL.le,← Real.rpow_add hL,← Real.rpow_mul_natCast hL.le]
      congr 1
      ring

end ArtinMatthews
