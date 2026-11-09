module

public import ArtinMatthews.ShiftedVoronoiBessel


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Complex
noncomputable section

theorem spectral_besselJ_nat_hasSum (n : ℕ) (z : ℂ) :
    HasSum (fun m : ℕ =>
      (z / 2) ^ n * (-((z / 2) ^ 2)) ^ m /
        ((m.factorial : ℂ) * ((m + n).factorial : ℂ)))
      (Complex.besselJ (n : ℂ) z) := by
  have hs := (Complex.regularizedHGFunSeries 0 {(n : ℂ) + 1}).hasSum
    (x := -((z / 2) ^ 2)) (by simp)
  have hΓ (m : ℕ) : Complex.Gamma ((n : ℂ) + 1 + m) =
      ((m + n).factorial : ℂ) := by
    convert Complex.Gamma_nat_eq_factorial (m + n) using 1 <;> push_cast <;> ring
  have hs' := hs.mul_left ((z / 2) ^ n)
  convert hs' using 1
  · funext m
    simp only [Complex.regularizedHGFunSeries, FormalMultilinearSeries.ofScalars_apply_eq,
      smul_eq_mul, Complex.regularizedHGFunCoeff, Multiset.map_zero, Multiset.prod_zero,
      Multiset.map_singleton, Multiset.prod_singleton, hΓ]
    ring
  · simp only [Complex.besselJ, Complex.cpow_natCast,
      Complex.regularizedHGFun, Complex.regularizedHGFunSeries]

theorem spectral_besselJ_nat_continuous (n : ℕ) :
    Continuous (Complex.besselJ (n : ℂ)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  simpa using (Complex.analyticAt_besselJ_int (n : ℤ) z).continuousAt

theorem spectral_besselJ_nat_norm_le (n : ℕ) (z : ℂ) :
    ‖Complex.besselJ (n : ℂ) z‖ ≤
      ‖z / 2‖ ^ n / (n.factorial : ℝ) * Real.exp (‖z / 2‖ ^ 2) := by
  simp only [norm_div]
  let t : ℝ := ‖z‖ / ‖(2 : ℂ)‖
  have hs := (NormedSpace.expSeries_div_hasSum_exp (t ^ 2)).mul_left
    (t ^ n / (n.factorial : ℝ))
  apply (spectral_besselJ_nat_hasSum n z).norm_le_of_bounded
    (by simpa only [← Real.exp_eq_exp_ℝ] using hs)
  intro m
  simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_natCast]
  have hn : (n.factorial : ℝ) ≤ (m + n).factorial := by
    exact_mod_cast Nat.factorial_le (show n ≤ m + n by omega)
  change t ^ n * (t ^ 2) ^ m / ((m.factorial : ℝ) * ((m + n).factorial : ℝ)) ≤
    t ^ n / (n.factorial : ℝ) * ((t ^ 2) ^ m / (m.factorial : ℝ))
  calc
    _ ≤ t ^ n * (t ^ 2) ^ m / ((m.factorial : ℝ) * (n.factorial : ℝ)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _))
    _ = _ := by rw [div_mul_div_comm]; ring

theorem spectral_besselJ_nat_norm_le_real (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ‖Complex.besselJ (n : ℂ) (x : ℂ)‖ ≤
      (x / 2) ^ n / (n.factorial : ℝ) * Real.exp (x ^ 2 / 4) := by
  have hcast : (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) := by norm_num [Complex.ofReal_div]
  have hnorm : ‖(x : ℂ) / 2‖ = x / 2 := by
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hsq : (x / 2) ^ 2 = x ^ 2 / 4 := by ring
  simpa only [hnorm, hsq] using spectral_besselJ_nat_norm_le n (x : ℂ)

end
end ArtinMatthews
