module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Analysis.SpecificLimits.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine dyadic majorant for the fourth-power principal spectral
weight. The cutoff cost keeps the linear term separate. -/
namespace ArtinMatthews
open Set
noncomputable section

def spectralPrincipalDecayWeight (Z t : ℝ) : ℝ :=
  1/(1+|t|/Z)^4

def spectralPrincipalDyadicRadius (Z : ℝ) (k : ℕ) : ℝ :=
  2*(2 : ℝ)^k*Z

theorem spectralPrincipalDecayWeight_nonneg (Z t : ℝ) :
    0 ≤ spectralPrincipalDecayWeight Z t := by
  unfold spectralPrincipalDecayWeight
  positivity

theorem spectralPrincipalDyadicRadius_ge_one {Z : ℝ} (hZ : 1 ≤ Z) (k : ℕ) :
    1 ≤ spectralPrincipalDyadicRadius Z k := by
  have hk : 1 ≤ (2 : ℝ)^k := one_le_pow₀ (by norm_num)
  unfold spectralPrincipalDyadicRadius
  nlinarith

theorem spectralPrincipalDecayWeight_dyadic {Z : ℝ} (hZ : 1 ≤ Z) (t : ℝ) :
    ∃ k : ℕ, 1+|t| ≤ spectralPrincipalDyadicRadius Z k ∧
      spectralPrincipalDecayWeight Z t ≤ (1/16 : ℝ)^k := by
  have hZ₀ : 0 < Z := zero_lt_one.trans_le hZ
  have hden : 1 ≤ 1+|t|/Z := by
    linarith [div_nonneg (abs_nonneg t) hZ₀.le]
  by_cases ht : 1+|t| ≤ Z
  · refine ⟨0,?_,?_⟩
    · simpa only [spectralPrincipalDyadicRadius,pow_zero,mul_one] using
        ht.trans (by linarith : Z ≤ 2*Z)
    · simpa only [spectralPrincipalDecayWeight,pow_zero,one_div_one] using
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (one_le_pow₀ (n := 4) hden)
  · let y := (1+|t|)/Z
    let m := ⌊y⌋₊
    let k := Nat.log 2 m
    have hy : 1 ≤ y := by
      dsimp [y]
      exact (one_le_div hZ₀).mpr (le_of_lt (lt_of_not_ge ht))
    have hm : 1 ≤ m := (Nat.le_floor_iff' (by decide : (1 : ℕ) ≠ 0)).mpr (by exact_mod_cast hy)
    have hlo : (2 : ℝ)^k ≤ y := by
      have hn := Nat.pow_log_le_self 2 (show m ≠ 0 by omega)
      have hreal : (2 : ℝ)^k ≤ (m : ℝ) := by exact_mod_cast hn
      exact hreal.trans (Nat.floor_le (zero_le_one.trans hy))
    have hhi : y ≤ 2*(2 : ℝ)^k := by
      have hn := Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) m
      have hc : (m : ℝ)+1 ≤ (2 : ℝ)^(k+1) := by
        exact_mod_cast (Nat.succ_le_of_lt hn)
      have he := (Nat.lt_floor_add_one y).le.trans hc
      rw [pow_succ] at he
      linarith
    have hcomp : y ≤ 1+|t|/Z := by
      have hdiv : (1 : ℝ)/Z ≤ 1 := (div_le_one hZ₀).mpr hZ
      dsimp [y]
      rw [add_div]
      linarith
    refine ⟨k,?_,?_⟩
    · unfold spectralPrincipalDyadicRadius
      exact (div_le_iff₀ hZ₀).mp hhi
    · have hp : ((2 : ℝ)^k)^4 ≤ (1+|t|/Z)^4 :=
        pow_le_pow_left₀ (pow_nonneg (by norm_num) k) (hlo.trans hcomp) 4
      have hh : spectralPrincipalDecayWeight Z t ≤ 1/((2 : ℝ)^k)^4 :=
        one_div_le_one_div_of_le (pow_pos (pow_pos (by norm_num) k) 4) hp
      apply hh.trans_eq
      rw [← pow_mul, Nat.mul_comm k 4, pow_mul, ← one_div_pow]
      norm_num

theorem spectralPrincipalDyadic_cost {B C Z : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hZ : 0 ≤ Z) (k : ℕ) :
    (1/16 : ℝ)^k *
      (C*((spectralPrincipalDyadicRadius Z k)^2+B*spectralPrincipalDyadicRadius Z k)) ≤
      (4*C*(Z^2+B*Z))*(1/4 : ℝ)^k := by
  have hq4 : (1/16 : ℝ)^k*((2 : ℝ)^k)^2 = (1/4 : ℝ)^k := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul, ← mul_pow]
    norm_num
  have hq2 : (1/16 : ℝ)^k*(2 : ℝ)^k = (1/8 : ℝ)^k := by
    rw [← mul_pow]
    norm_num
  have hq : (1/8 : ℝ)^k ≤ (1/4 : ℝ)^k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
  calc
    _ = 4*C*Z^2*((1/16 : ℝ)^k*((2 : ℝ)^k)^2) +
        2*C*B*Z*((1/16 : ℝ)^k*(2 : ℝ)^k) := by
      unfold spectralPrincipalDyadicRadius
      ring
    _ = 4*C*Z^2*(1/4 : ℝ)^k+2*C*B*Z*(1/8 : ℝ)^k := by rw [hq4,hq2]
    _ ≤ 4*C*Z^2*(1/4 : ℝ)^k+4*C*B*Z*(1/4 : ℝ)^k := by
      gcongr
      norm_num
    _ = _ := by ring

end
end ArtinMatthews
