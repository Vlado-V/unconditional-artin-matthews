module

import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv


set_option backward.privateInPublic true
@[expose] public section

/-! The actual prime-power terms and local logarithmic derivative of a
Dedekind Euler factor.  These elementary identities are independent of the
number field and are used before summing over its prime ideals. -/

noncomputable section

namespace ArtinMatthews.VaryingKummerAnalytic

def primePowerMangoldtTerm (N n : ℕ) (s : ℂ) : ℂ :=
  (Real.log N : ℂ) * ((N : ℂ) ^ (-s)) ^ (n + 1)

def primePowerMangoldtLocal (N : ℕ) (s : ℂ) : ℂ :=
  (Real.log N : ℂ) * ((N : ℂ) ^ (-s) / (1 - (N : ℂ) ^ (-s)))

theorem primePowerMangoldt_ratio_norm_lt_one {N : ℕ} (hN : 2 ≤ N)
    {s : ℂ} (hs : 1 < s.re) :
    ‖(N : ℂ) ^ (-s)‖ < 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNone : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hNpos,
    Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg hNone (by linarith)

/-- The positive-power geometric series gives the actual local Euler logarithmic derivative. -/
theorem primePowerMangoldtTerm_hasSum {N : ℕ} (hN : 2 ≤ N)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => primePowerMangoldtTerm N n s) (primePowerMangoldtLocal N s) := by
  let q : ℂ := (N : ℂ) ^ (-s)
  have h := ((hasSum_geometric_of_norm_lt_one
    (primePowerMangoldt_ratio_norm_lt_one hN hs)).mul_left q).mul_left (Real.log N : ℂ)
  convert h using 1
  · ext n
    simp only [primePowerMangoldtTerm, q, pow_succ]
    ring
  · simp only [primePowerMangoldtLocal, q, div_eq_mul_inv]

/-- The term norm equals its positive real-axis value at the same real part. -/
theorem primePowerMangoldtTerm_norm_eq_real {N : ℕ} (hN : 2 ≤ N)
    (n : ℕ) (s : ℂ) :
    ‖primePowerMangoldtTerm N n s‖ = (primePowerMangoldtTerm N n (s.re : ℂ)).re := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hcpow : (N : ℂ) ^ (-(s.re : ℂ)) = Complex.ofReal ((N : ℝ) ^ (-s.re)) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow hNpos.le]
  simp only [primePowerMangoldtTerm, hcpow, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, Complex.ofReal_re, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hNpos,
    Complex.neg_re]

/-- Absolute convergence, with its precise positive real-axis local sum. -/
theorem primePowerMangoldtTerm_norm_hasSum {N : ℕ} (hN : 2 ≤ N)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => ‖primePowerMangoldtTerm N n s‖)
      (primePowerMangoldtLocal N (s.re : ℂ)).re := by
  simpa only [primePowerMangoldtTerm_norm_eq_real hN] using
    Complex.hasSum_re (primePowerMangoldtTerm_hasSum hN
      (s := (s.re : ℂ)) (by simpa using hs))

/-- Differentiating the actual principal-branch Euler logarithm introduces
the negative of the positive Mangoldt local series. -/
theorem primePowerMangoldtLog_hasDerivAt {N : ℕ} (hN : 2 ≤ N)
    {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (fun z : ℂ => -Complex.log (1 - (N : ℂ) ^ (-z)))
      (-primePowerMangoldtLocal N s) s := by
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hslit : 1 - (N : ℂ) ^ (-s) ∈ Complex.slitPlane := by
    simpa only [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one
      (z := -(N : ℂ) ^ (-s)) (by simpa using primePowerMangoldt_ratio_norm_lt_one hN hs)
  have hcpow := (hasDerivAt_id s).neg.const_cpow (c := (N : ℂ)) (Or.inl hNne)
  have hd := (((hasDerivAt_const s (1 : ℂ)).sub hcpow).clog hslit).neg
  have hlog : Complex.log (N : ℂ) = (Real.log N : ℂ) := by
    simpa only [Complex.ofReal_natCast] using
      (Complex.ofReal_log (show (0 : ℝ) ≤ N by positivity)).symm
  convert hd using 1
  · rfl
  · change -((Real.log N : ℂ) * ((N : ℂ) ^ (-s) / (1 - (N : ℂ) ^ (-s)))) =
      -((0 - (N : ℂ) ^ (-s) * Complex.log (N : ℂ) * -1) / (1 - (N : ℂ) ^ (-s)))
    rw [hlog]
    ring

end ArtinMatthews.VaryingKummerAnalytic
