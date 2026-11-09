module

public import ArtinMatthews.SpectralABLWindows


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open scoped BigOperators
noncomputable section

def spectralABLExceptionalBound (A : ℕ) : ℝ :=
  4 * ((2 * (A : ℝ) + 1) ^ 2) ^ (A + 1)

theorem spectralABLExceptionalWindowReal_decay (a : ℝ) {A : ℕ} (hA : 1 ≤ A) (t : ℝ) :
    spectralABLExceptionalWindowReal a A t ≤
      spectralABLExceptionalBound A / (1 + t ^ 2) ^ (A - 1) := by
  let B := (2 * (A : ℝ) + 1) ^ 2
  let u := 1 + t ^ 2
  have hA' : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hB : 1 ≤ B := by dsimp [B]; nlinarith
  have hu : 0 < u := by dsimp [u]; positivity
  have hcos : (2 * Real.cos (2 * t * Real.log a)) ^ 2 ≤ 4 := by
    have hc := Real.abs_cos_le_one (2 * t * Real.log a)
    rcases abs_le.mp hc with ⟨hl, hr⟩
    nlinarith
  have hbase : u ≤ t ^ 2 + (2 * (A : ℝ)) ^ 2 := by dsimp [u]; nlinarith
  have hden : u ^ (2 * A) ≤ (t ^ 2 + (2 * (A : ℝ)) ^ 2) ^ (2 * A) :=
    pow_le_pow_left₀ hu.le hbase _
  have hfrac : (2 * Real.cos (2 * t * Real.log a)) ^ 2 /
      (t ^ 2 + (2 * (A : ℝ)) ^ 2) ^ (2 * A) ≤ 4 / u ^ (2 * A) := by
    exact (div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hu _) hden).trans
      (div_le_div_of_nonneg_right hcos (pow_nonneg hu.le _))
  have hfactor (k : ℕ) (hk : k ∈ Finset.range (A + 1)) :
      t ^ 2 + (((2 * k + 1 : ℕ) : ℝ) / 2) ^ 2 ≤ B * u := by
    have hkA : k ≤ A := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hkA' : (k : ℝ) ≤ A := by exact_mod_cast hkA
    have hc : (((2 * k + 1 : ℕ) : ℝ) / 2) ^ 2 ≤ B := by
      dsimp [B]
      push_cast
      nlinarith [sq_nonneg (k : ℝ), sq_nonneg (A : ℝ)]
    dsimp [u]
    nlinarith [mul_nonneg (sub_nonneg.mpr hB) (sq_nonneg t)]
  have hprod : (∏ k ∈ Finset.range (A + 1),
      (t ^ 2 + (((2 * k + 1 : ℕ) : ℝ) / 2) ^ 2)) ≤ (B * u) ^ (A + 1) := by
    calc
      _ ≤ ∏ _k ∈ Finset.range (A + 1), B * u :=
        Finset.prod_le_prod₀ (fun _ _ => by positivity) hfactor
      _ = _ := by simp
  change _ ≤ (4 * B ^ (A + 1)) / u ^ (A - 1)
  unfold spectralABLExceptionalWindowReal
  calc
    _ ≤ (4 / u ^ (2 * A)) * (B * u) ^ (A + 1) :=
      mul_le_mul hfrac hprod (Finset.prod_nonneg fun _ _ => by positivity) (by positivity)
    _ = _ := by
      have hpow : 2 * A = (A + 1) + (A - 1) := by omega
      rw [hpow, pow_add, mul_pow]
      field_simp

theorem spectralABLExceptionalWindow_norm_le (a : ℝ) {A : ℕ} (hA : 1 ≤ A) (t : ℝ) :
    ‖spectralABLExceptionalWindow a A (t : ℂ)‖ ≤ spectralABLExceptionalBound A := by
  rw [spectralABLExceptionalWindow_real, Complex.norm_real,
    Real.norm_of_nonneg (spectralABLExceptionalWindowReal_nonneg a A t)]
  refine (spectralABLExceptionalWindowReal_decay a hA t).trans ?_
  have hden : 1 ≤ (1 + t ^ 2) ^ (A - 1) := one_le_pow₀ (by nlinarith [sq_nonneg t])
  exact div_le_self (by unfold spectralABLExceptionalBound; positivity) hden

end
end ArtinMatthews
