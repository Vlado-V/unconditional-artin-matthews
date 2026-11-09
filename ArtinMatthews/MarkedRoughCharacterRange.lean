module

public import ArtinMatthews.MarkedRoughCharacterBudget
public import Mathlib.Algebra.Order.Floor.Semiring


set_option backward.privateInPublic true
@[expose] public section

/-! The divisor, frequency, and logarithmic sieve-depth ranges used by
the actual rough-character estimate. -/

namespace ArtinMatthews

open Filter
open scoped Topology

theorem marked_rough_divisor_length {τ L H d : ℝ} (hd : 0 < d)
    (hdhi : d ≤ Real.exp (τ*L/2)) (hH : Real.exp (τ*L) ≤ H) :
    Real.exp (τ*L/2) ≤ H/d := by
  apply (le_div_iff₀ hd).mpr
  calc
    _ ≤ Real.exp (τ*L/2)*Real.exp (τ*L/2) :=
      mul_le_mul_of_nonneg_left hdhi (Real.exp_nonneg _)
    _ = Real.exp (τ*L) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ H := hH

theorem marked_rough_frequency_range {τ L H d t B : ℝ}
    (hτ : 0 < τ) (hL : 0 ≤ L) (hd : 0 < d)
    (hdhi : d ≤ Real.exp (τ*L/2)) (hH : Real.exp (τ*L) ≤ H)
    (ht : |t| ≤ Real.exp (2*L)) (hB : 4/τ ≤ B) :
    |t/(2*Real.pi)| ≤ (H/d)^B := by
  have hB0 : 0 ≤ B := (div_nonneg (by norm_num) hτ.le).trans hB
  have hfreq : |t/(2*Real.pi)| ≤ Real.exp (2*L) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2*Real.pi)]
    calc
      _ ≤ |t| := div_le_self (abs_nonneg _) (by nlinarith [Real.two_le_pi])
      _ ≤ _ := ht
  have hpower := Real.rpow_le_rpow (Real.exp_nonneg (τ*L/2))
    (marked_rough_divisor_length hd hdhi hH) hB0
  calc
    _ ≤ Real.exp (2*L) := hfreq
    _ ≤ (Real.exp (τ*L/2))^B := by
      rw [← Real.exp_mul]
      apply Real.exp_le_exp.mpr
      have hh : 4 ≤ B*τ := (div_le_iff₀ hτ).mp hB
      nlinarith [mul_nonneg (show 0 ≤ B*τ-4 by linarith) hL]
    _ ≤ _ := hpower

theorem marked_rough_log_depth_ratio_tendsto (C ρ : ℝ) (hρ : ρ < 1) :
    Tendsto (fun L : ℝ => (C*Real.log L+1)/L^(1-ρ)) atTop (𝓝 0) := by
  have h₁ := ((isLittleO_log_rpow_atTop (show 0 < 1-ρ by linarith)).tendsto_div_nhds_zero).const_mul C
  have h₂ := tendsto_rpow_neg_atTop (show 0 < 1-ρ by linarith)
  have hh := h₁.add h₂
  simp only [mul_zero, add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  rw [Real.rpow_neg hL.le]
  change C*(Real.log L/L^(1-ρ))+(L^(1-ρ))⁻¹ = _
  ring

/-- A logarithmic Bonferroni depth uses a vanishing fraction of a
positive exponential length scale. -/
theorem marked_rough_log_depth_length (C ρ θ : ℝ)
    (hC : 0 ≤ C) (hρ : ρ < 1) (hθ : 0 < θ) :
    ∀ᶠ L : ℝ in atTop,
      L^ρ*((⌊C*Real.log L⌋₊+1 : ℕ) : ℝ) ≤ θ*L := by
  have hs := (marked_rough_log_depth_ratio_tendsto C ρ hρ).eventually (Iio_mem_nhds hθ)
  filter_upwards [hs, eventually_ge_atTop (1 : ℝ)] with L hs hL
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have harg : 0 ≤ C*Real.log L := mul_nonneg hC (Real.log_nonneg hL)
  have hfloor : ((⌊C*Real.log L⌋₊+1 : ℕ) : ℝ) ≤ C*Real.log L+1 := by
    simp only [Nat.cast_add, Nat.cast_one]
    linarith [Nat.floor_le harg]
  have hratio : C*Real.log L+1 ≤ θ*L^(1-ρ) :=
    ((div_lt_iff₀ (Real.rpow_pos_of_pos hL0 _)).mp hs).le
  calc
    _ ≤ L^ρ*(C*Real.log L+1) := mul_le_mul_of_nonneg_left hfloor (Real.rpow_nonneg hL0.le _)
    _ ≤ L^ρ*(θ*L^(1-ρ)) := mul_le_mul_of_nonneg_left hratio (Real.rpow_nonneg hL0.le _)
    _ = θ*L := by rw [mul_left_comm, ← Real.rpow_add hL0]; simp

theorem marked_rough_log_depth_support (C ρ θ : ℝ)
    (hC : 0 ≤ C) (hρ : ρ < 1) (hθ : 0 < θ) :
    ∀ᶠ L : ℝ in atTop,
      (Real.exp (L^ρ))^(⌊C*Real.log L⌋₊+1) ≤ Real.exp (θ*L) := by
  filter_upwards [marked_rough_log_depth_length C ρ θ hC hρ hθ] with L hL
  rw [← Real.rpow_natCast, ← Real.exp_mul]
  exact Real.exp_le_exp.mpr hL

theorem marked_rough_actual_depth_support (C τ : ℝ) (hC : 0 ≤ C) (hτ : 0 < τ) :
    ∀ᶠ L : ℝ in atTop,
      (Real.exp (L^(6/25 : ℝ)))^(⌊C*Real.log L⌋₊+1) ≤ Real.exp (τ*L/2) := by
  have hh := marked_rough_log_depth_support C (6/25) (τ/2) hC (by norm_num) (half_pos hτ)
  simpa only [div_mul_eq_mul_div] using hh

theorem marked_rough_cutoff_scale (κ γ : ℝ) (hκ : κ < 1) (hγ : 0 < γ) :
    ∀ᶠ L : ℝ in atTop, Real.exp (L^κ) ≤ Real.exp (γ*L) := by
  simpa using marked_rough_log_depth_support 0 κ γ (by norm_num) hκ hγ

theorem marked_rough_log_cutoff_le_power (κ γ : ℝ) (hκ : κ < 1) (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, Real.exp ((Real.log x)^κ) ≤ x^γ := by
  filter_upwards [Real.tendsto_log_atTop.eventually (marked_rough_cutoff_scale κ γ hκ hγ),
    eventually_gt_atTop (0 : ℝ)] with x hx hx0
  rw [Real.rpow_def_of_pos hx0]
  simpa only [mul_comm] using hx

end ArtinMatthews
