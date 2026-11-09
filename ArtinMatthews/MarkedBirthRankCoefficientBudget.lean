module

public import ArtinMatthews.MarkedBirthRankCutoff


set_option backward.privateInPublic true
@[expose] public section

/-! Actual fixed-K coefficient bases and boundary constants are absorbed
uniformly at the literal growing moment length. -/

noncomputable section
namespace ArtinMatthews
open Filter

theorem markedBirthRankCoefficientBase_polynomial (K : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      ((markedMemoryPotentialAddressCount K x:ℝ)^2+1)^2 ≤ (Real.log x)^13 := by
  let C := ((16*(K:ℝ))^2+1)^2
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 C))] with x hx
  have hL : 1 ≤ Real.log x := (le_max_left _ _).trans hx
  have hC : C ≤ Real.log x := (le_max_right _ _).trans hx
  have hQ := markedMemoryPotentialAddressCount_polynomial K hL
  have hQ2 := pow_le_pow_left₀ (Nat.cast_nonneg (markedMemoryPotentialAddressCount K x)) hQ 2
  have hL6 : 1 ≤ (Real.log x)^6 := one_le_pow₀ hL
  have hbase : (markedMemoryPotentialAddressCount K x:ℝ)^2+1 ≤
      ((16*(K:ℝ))^2+1)*(Real.log x)^6 := by nlinarith [hQ2]
  calc
    _ ≤ (((16*(K:ℝ))^2+1)*(Real.log x)^6)^2 :=
      pow_le_pow_left₀ (by positivity) hbase 2
    _ = C*(Real.log x)^12 := by dsimp [C]; ring
    _ ≤ (Real.log x)*(Real.log x)^12 := mul_le_mul_of_nonneg_right hC (pow_nonneg (zero_le_one.trans hL) _)
    _ = _ := by ring

private theorem two_mul_nat_le_two_pow (n : ℕ) : 2*n ≤ 2^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    by_cases hn : n = 0
    · subst n; norm_num
    · have hn₁ : 1 ≤ n := by omega
      rw [pow_succ]
      omega

theorem markedBirthRank_boundary_prefactor_eventually {C : ℝ} (hC : 1 ≤ C) :
    ∀ᶠ x : ℝ in atTop,
      2*(markedMemoryMomentLength x:ℝ)*C^(markedMemoryMomentLength x+1) ≤
        ((Real.log x)^(1/2:ℝ))^(markedMemoryMomentLength x) := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 ((2*C^2)^2)))] with x hx
  have hL : 1 ≤ Real.log x := (le_max_left _ _).trans hx
  have hN₀ : 1 ≤ (markedMemoryMomentLength x:ℝ) :=
    (Real.one_le_rpow hL (by norm_num : (0:ℝ) ≤ 1/2)).trans (markedMemoryMomentLength_lower (zero_le_one.trans hL))
  have hN : 1 ≤ markedMemoryMomentLength x := by exact_mod_cast hN₀
  have hC₀ : 0 ≤ C := zero_le_one.trans hC
  have hbase : 2*C^2 ≤ (Real.log x)^(1/2:ℝ) := by
    have hh := (le_max_right _ _).trans hx
    rw [← Real.sqrt_eq_rpow]
    exact (Real.le_sqrt (by positivity) (zero_le_one.trans hL)).mpr hh
  have hnreal : 2*(markedMemoryMomentLength x:ℝ) ≤ (2:ℝ)^(markedMemoryMomentLength x) := by
    exact_mod_cast two_mul_nat_le_two_pow (markedMemoryMomentLength x)
  calc
    _ ≤ (2:ℝ)^(markedMemoryMomentLength x)*C^(2*markedMemoryMomentLength x) :=
      mul_le_mul hnreal (pow_le_pow_right₀ hC (by omega)) (pow_nonneg hC₀ _) (by positivity)
    _ = (2*C^2)^(markedMemoryMomentLength x) := by rw [mul_pow,pow_mul]
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hbase _

end ArtinMatthews
