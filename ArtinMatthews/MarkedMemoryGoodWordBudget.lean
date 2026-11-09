module

public import ArtinMatthews.MarkedMinorArcRawGhostEnergyBound


set_option backward.privateInPublic true
@[expose] public section

/-! Fixed ghost constants are absorbed uniformly in every positive word
length. The choice of rho is explicit and satisfies the actual ghost gap. -/

noncomputable section
namespace ArtinMatthews
open Filter

def markedMemoryChosenRho (q : ℝ) : ℝ := Real.sqrt ((1+Real.sqrt q)/2)

theorem markedMemoryChosenRho_bounds {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    0 < markedMemoryChosenRho q ∧ markedMemoryChosenRho q < 1 ∧
      Real.sqrt q < (markedMemoryChosenRho q)^2 := by
  have hs₀ := Real.sqrt_nonneg q
  have hs₁ : Real.sqrt q < 1 := by
    nlinarith [Real.sq_sqrt hq₀]
  have hp : 0 < (1+Real.sqrt q)/2 := by positivity
  have he : (markedMemoryChosenRho q)^2 = (1+Real.sqrt q)/2 := Real.sq_sqrt hp.le
  have hr : 0 < markedMemoryChosenRho q := Real.sqrt_pos.2 hp
  refine ⟨hr, ?_, ?_⟩ <;> nlinarith

theorem markedMemory_word_constant_budget {C : ℝ} (hC : 1 ≤ C) (G : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, 0 < n →
      2*C^(n+1)*((Real.log x)^(-(G+2)))^n ≤ ((Real.log x)^(-G))^n := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max 1 (2*C^2)))] with x hx
  have hL₁ : 1 ≤ Real.log x := (le_max_left _ _).trans hx
  have hL : 0 < Real.log x := zero_lt_one.trans_le hL₁
  have hCL : 2*C^2 ≤ (Real.log x)^2 := by
    have h := (le_max_right _ _).trans hx
    nlinarith
  intro n hn
  have hC₀ : 0 ≤ C := zero_le_one.trans hC
  have hε : 0 ≤ (Real.log x)^(-(G+2)) := Real.rpow_nonneg hL.le _
  have hcoeff : 2*C^(n+1) ≤ (2*C^2)^n := by
    have hn' : n+1 ≤ 2*n := by omega
    have hc := pow_le_pow_right₀ hC hn'
    have ht : (2:ℝ) ≤ 2^n := by
      simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hn
    calc
      2*C^(n+1) ≤ 2^n*C^(2*n) := mul_le_mul ht hc (pow_nonneg hC₀ _) (by positivity)
      _ = (2*C^2)^n := by rw [mul_pow, pow_mul]
  have heq : (Real.log x)^2*(Real.log x)^(-(G+2)) = (Real.log x)^(-G) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL]
    congr 1
    ring
  calc
    _ ≤ (2*C^2)^n*((Real.log x)^(-(G+2)))^n :=
      mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hε _)
    _ = (2*C^2*(Real.log x)^(-(G+2)))^n := (mul_pow _ _ _).symm
    _ ≤ ((Real.log x)^2*(Real.log x)^(-(G+2)))^n :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hCL hε) n
    _ = _ := by rw [heq]

end ArtinMatthews
