module

public import ArtinMatthews.ProbePrimeLocalCoefficient
public import ArtinMatthews.ProbeEulerRegions


set_option backward.privateInPublic true
@[expose] public section

/-! Norm and support bounds for the genuine local finite sums at a prime
dividing the sixth-free parameter. No estimate for C is an input. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped NumberField Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem probePrimeNorm_one_le (p : 𝓞 K) (hp : p ≠ 0) :
    1 ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp))

theorem probePrimeTau_norm_le_sqrt (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) :
    ‖probePrimeTau K p hp.ne_zero χ‖ ≤ Real.sqrt (Ideal.absNorm (Ideal.span {p}) : ℝ) := by
  by_cases hχ : χ = 1
  · rw [hχ, probePrimeTau_principal K p hp, norm_neg, norm_one]
    have hQ := probePrimeNorm_one_le K p hp.ne_zero
    nlinarith [Real.sqrt_nonneg (Ideal.absNorm (Ideal.span {p}) : ℝ),
      Real.sq_sqrt (by positivity : 0 ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ))]
  · exact (probePrimeTau_norm K p hp χ hχ).le

theorem probePrimeResidueTransform_prime_pow_norm_le (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6) (v J : ℕ) :
    ‖probePrimeResidueTransform K p hp.ne_zero χ v (p ^ J)‖ ≤
      (Ideal.absNorm (Ideal.span {p}) : ℝ) := by
  have hQ := probePrimeNorm_one_le K p hp.ne_zero
  rw [probePrimeResidueTransform_prime_pow K p hp χ hχ]
  split_ifs
  · apply (probePrimeTau_norm_le_sqrt K p hp (χ ^ v)).trans
    nlinarith [Real.sqrt_nonneg (Ideal.absNorm (Ideal.span {p}) : ℝ),
      Real.sq_sqrt (by positivity : 0 ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ))]
  · have hreal : (Ideal.absNorm (Ideal.span {p}) : ℂ) - 1 =
        (((Ideal.absNorm (Ideal.span {p}) : ℝ) - 1 : ℝ) : ℂ) := by
      simp only [Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_one]
    rw [hreal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  · simp only [norm_zero]
    positivity

theorem probePrimeLocalCZero_norm_le (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6) (n J : ℕ) :
    ‖probePrimeLocalCZero K p hp.ne_zero χ n J‖ ≤
      (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (n + 1) := by
  rw [probePrimeLocalCZero_eq K p hp χ]
  split_ifs
  · rw [norm_mul, norm_pow, Complex.norm_natCast, pow_succ]
    exact mul_le_mul_of_nonneg_left
      (probePrimeResidueTransform_prime_pow_norm_le K p hp χ hχ _ _) (by positivity)
  · simp

theorem probePrimeLocalCOne_norm_le (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (n J : ℕ) :
    ‖probePrimeLocalCOne K p hp.ne_zero χ n J‖ ≤
      Real.sqrt (Ideal.absNorm (Ideal.span {p}) : ℝ) *
        (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (n + 1) := by
  rw [probePrimeLocalCOne_eq K p hp χ hminus]
  split_ifs
  · rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast, pow_succ, ← mul_assoc]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right (probePrimeTau_norm_le_sqrt K p hp χ) (by positivity))
      (probePrimeResidueTransform_prime_pow_norm_le K p hp χ hχ _ _)
      (norm_nonneg _) (by positivity)
  · simp only [norm_zero]
    positivity

theorem probePrimeLocalCoefficient_zero_norm_le (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6) (t J : ℕ) :
    ‖probePrimeLocalCoefficient K p hp.ne_zero χ t 0 J‖ ≤
      (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ t := by
  cases t with
  | zero => simp [probePrimeLocalCoefficient_zero_zero]
  | succ n => exact probePrimeLocalCZero_norm_le K p hp χ hχ n J

theorem probePrimeLocalCoefficient_one_norm_le (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (t J : ℕ) :
    ‖probePrimeLocalCoefficient K p hp.ne_zero χ t 1 J‖ ≤
      Real.sqrt (Ideal.absNorm (Ideal.span {p}) : ℝ) *
        (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ t := by
  cases t with
  | zero =>
    change ‖probePrimeLocalInnerAbsent K p χ 0 J‖ ≤ _
    rw [probePrimeLocalInnerAbsent_eq K p hp χ, pow_zero, mul_one]
    split_ifs
    · have hQ := probePrimeNorm_one_le K p hp.ne_zero
      simp only [norm_one]
      nlinarith [Real.sqrt_nonneg (Ideal.absNorm (Ideal.span {p}) : ℝ),
        Real.sq_sqrt (by positivity : 0 ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ))]
    · simp
  | succ n => exact probePrimeLocalCOne_norm_le K p hp χ hχ hminus n J

theorem probePrimeLocalCoefficient_zero_bad_outer (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (k J : ℕ) (hJ : 0 < J) :
    probePrimeLocalCoefficient K p hp.ne_zero χ 0 (k + 1) J = 0 := by
  change probePrimeLocalInnerAbsent K p χ k J = 0
  rw [probePrimeLocalInnerAbsent_eq K p hp χ, ite_eq_right (by omega)]

theorem probePrimeLocalCoefficient_bad_higher (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (t k J : ℕ) (hJ : 0 < J) :
    probePrimeLocalCoefficient K p hp.ne_zero χ t (k + 2) J = 0 := by
  cases t with
  | zero => exact probePrimeLocalCoefficient_zero_bad_outer K p hp χ (k + 1) J hJ
  | succ n => exact probePrimeLocalCoefficient_higher K p hp χ n k J

theorem probePrimeLocalCoefficient_bad_first_zero (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (J : ℕ) (hJ : 0 < J) :
    probePrimeLocalCoefficient K p hp.ne_zero χ 1 0 J = 0 := by
  change probePrimeLocalCZero K p hp.ne_zero χ 0 J = 0
  rw [probePrimeLocalCZero_eq K p hp χ, ite_eq_left (Nat.zero_le _), pow_zero,
    Nat.sub_zero, one_mul, probePrimeResidueTransform_prime_pow K p hp χ hχ,
    ite_eq_right (by omega), ite_eq_right (by omega)]

end
end ArtinMatthews.VaryingKummerAnalytic
