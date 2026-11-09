module

public import ArtinMatthews.SpectralCuspEisensteinFourierIntegrals
public import ArtinMatthews.SpectralCuspEisensteinZeroRows
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Exact zero-sector and central-sign accounting for the nonzero
Fourier coefficients of the actual Eisenstein family. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups

namespace ArtinMatthews

theorem spectralRealFourierPhase_integral_nonzero (n : ℤ) (hn : n ≠ 0) :
    (∫ x in (0 : ℝ)..1,spectralRealFourierPhase (n : ℝ) x) = 0 := by
  let c : ℂ := -((cuspFourierFrequency 1 n : ℝ) : ℂ)*Complex.I
  have hfreq : cuspFourierFrequency 1 n ≠ 0 := by
    unfold cuspFourierFrequency
    rw [div_one]
    exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (by exact_mod_cast hn)
  have hc : c ≠ 0 := mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hfreq)) Complex.I_ne_zero
  have h1 : Complex.exp c = 1 := by
    simpa only [c,cuspFourierPhase,Complex.ofReal_one,mul_one] using cuspFourierPhase_period 1 one_pos n
  simp_rw [spectralRealFourierPhase_int]
  change (∫ x in (0 : ℝ)..1,Complex.exp (c*(x : ℂ))) = 0
  rw [integral_exp_mul_complex hc]
  simp [h1]

theorem cuspEisensteinRowFourierIntegral_zero (N : ℕ) [NeZero N]
    (r a : SL(2, ℤ)) (s : ℂ) (n : ℤ) (hn : n ≠ 0) (y : ℝ) (hy : 0 < y)
    (v : CuspEisensteinZeroRows N r a) :
    cuspEisensteinRowFourierIntegral N r a s n y hy v.val = 0 := by
  have hp (x : ℝ) : cuspEisensteinRowTerm N r a s v.val (cuspEisensteinTargetPoint N r y hy x) =
      (((gamma0CuspTrueWidth N r : ℝ)*y : ℝ) : ℂ)^s := by
    rw [cuspEisensteinRowTerm_zero]
    congr 1
    exact congrArg Complex.ofReal (cuspWidthDilation_im_smul _ _ _)
  unfold cuspEisensteinRowFourierIntegral
  simp_rw [hp]
  rw [integral_const_mul,← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    spectralRealFourierPhase_integral_nonzero n hn,mul_zero]

theorem cuspEisensteinRowFourierIntegral_signs (N : ℕ) [NeZero N]
    (r a : SL(2, ℤ)) (s : ℂ) (hs : 1 < s.re) (n : ℤ) (hn : n ≠ 0)
    (y : ℝ) (hy : 0 < y) :
    (∑' v : Gamma0CuspEisensteinRows N r a, cuspEisensteinRowFourierIntegral N r a s n y hy v) =
      2*(∑' v : CuspEisensteinPositiveRows N r a, cuspEisensteinRowFourierIntegral N r a s n y hy v.val) := by
  rw [cuspEisenstein_signed_tsum N r a _
    (cuspEisensteinRowFourierIntegral_summable N r a s hs n y hy)
    (fun v => cuspEisensteinRowFourierIntegral_neg N r a s n y hy v)]
  simp only [cuspEisensteinRowFourierIntegral_zero N r a s n hn y hy,tsum_zero,zero_add]

theorem gamma0CuspEisenstein_nonzero_fourier_positive_rows (N : ℕ) [NeZero N]
    (r a : SL(2, ℤ)) (s : ℂ) (hs : 1 < s.re) (n : ℤ) (hn : n ≠ 0)
    (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1,gamma0CuspEisenstein N a s
      (gamma0TrueCuspScaling N r • gamma0EisensteinHorizontalPoint y hy x)*
        spectralRealFourierPhase (n : ℝ) x) =
      (gamma0CuspTrueWidth N a : ℂ)^(-s)*
        (∑' v : CuspEisensteinPositiveRows N r a,
          cuspEisensteinRowFourierIntegral N r a s n y hy v.val) := by
  rw [gamma0CuspEisenstein_fourier_integral_rows N r a s hs n y hy,
    cuspEisensteinRowFourierIntegral_signs N r a s hs n hn y hy]
  ring

end ArtinMatthews

