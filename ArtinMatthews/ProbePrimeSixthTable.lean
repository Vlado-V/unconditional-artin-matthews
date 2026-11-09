module

public import ArtinMatthews.ProbePrimeGaussPhase


set_option backward.privateInPublic true
@[expose] public section

/-! The nonzero j=0 local coefficients, with J=6*r.  The index n still
means t=n+1.  These are evaluations of the literal frozen local sums. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped NumberField Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem probeSextic_power_reduce {R : Type*} [Monoid R] (x : R) (hx : x ^ 6 = 1)
    (d r : ℕ) : x ^ (6 * d + r) = x ^ r := by
  rw [pow_add, pow_mul, hx, one_pow, one_mul]

theorem probePrimeLocalCZero_off_classes (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (n r : ℕ) (hn : ¬ 6 ∣ n) (hn1 : ¬ 6 ∣ n + 1) :
    probePrimeLocalCZero K p hp.ne_zero χ n (6 * r) = 0 := by
  rw [probePrimeLocalCZero_eq K p hp χ]
  split_ifs with hnr
  · rw [probePrimeResidueTransform_prime_pow K p hp χ hχ]
    have hdiff : 6 * r - n ≠ 0 := by omega
    rw [ite_eq_right hdiff, ite_eq_right hn1, mul_zero]
  · rfl

theorem probePrimeLocalCOne_off_classes (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (n r : ℕ) (hn : ¬ 6 ∣ n) (hn1 : ¬ 6 ∣ n + 1) :
    probePrimeLocalCOne K p hp.ne_zero χ n (6 * r) = 0 := by
  rw [probePrimeLocalCOne_eq K p hp χ hminus]
  split_ifs with hnr
  · rw [probePrimeResidueTransform_prime_pow K p hp χ hχ]
    have hdiff : 6 * r - (n + 1) ≠ 0 := by omega
    rw [ite_eq_right hdiff, ite_eq_right hn, mul_zero]
  · rfl

theorem probePrimeLocalCZero_one_class (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6) (d r : ℕ) :
    probePrimeLocalCZero K p hp.ne_zero χ (6 * d) (6 * r) =
      if r = d then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (6 * d) *
        probePrimeTau K p hp.ne_zero χ else 0 := by
  have h6 : χ ^ 6 = 1 := (orderOf_dvd_iff_pow_eq_one).mp (by rw [hχ])
  rw [probePrimeLocalCZero_eq K p hp χ]
  by_cases hdr : r = d
  · subst r
    rw [ite_eq_left le_rfl, Nat.sub_self,
      probePrimeResidueTransform_prime_pow K p hp χ hχ, ite_eq_left rfl,
      ite_eq_left rfl, probeSextic_power_reduce χ h6 d 1, pow_one]
  · rw [ite_eq_right hdr]
    split_ifs with hle
    · rw [probePrimeResidueTransform_prime_pow K p hp χ hχ,
        ite_eq_right (by omega), ite_eq_right (by omega), mul_zero]
    · rfl

theorem probePrimeLocalCOne_one_class (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (d r : ℕ) :
    probePrimeLocalCOne K p hp.ne_zero χ (6 * d) (6 * r) =
      if d < r then probePrimeTau K p hp.ne_zero χ *
        (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (6 * d) *
          ((Ideal.absNorm (Ideal.span {p}) : ℂ) - 1) else 0 := by
  rw [probePrimeLocalCOne_eq K p hp χ hminus]
  by_cases hdr : d < r
  · rw [ite_eq_left (by omega), ite_eq_left hdr,
      probePrimeResidueTransform_prime_pow K p hp χ hχ,
      ite_eq_right (by omega), ite_eq_left (dvd_mul_right 6 d)]
  · rw [ite_eq_right (by omega), ite_eq_right hdr]

theorem probePrimeLocalCZero_zero_class (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6) (d r : ℕ) :
    probePrimeLocalCZero K p hp.ne_zero χ (6 * d + 5) (6 * r) =
      if d < r then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (6 * d + 5) *
        ((Ideal.absNorm (Ideal.span {p}) : ℂ) - 1) else 0 := by
  rw [probePrimeLocalCZero_eq K p hp χ]
  by_cases hdr : d < r
  · rw [ite_eq_left (by omega), ite_eq_left hdr,
      probePrimeResidueTransform_prime_pow K p hp χ hχ,
      ite_eq_right (by omega), ite_eq_left (by omega)]
  · rw [ite_eq_right (by omega), ite_eq_right hdr]

theorem probePrimeLocalCOne_zero_class (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (d r : ℕ) :
    probePrimeLocalCOne K p hp.ne_zero χ (6 * d + 5) (6 * r) =
      if r = d + 1 then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (6 * d + 6) else 0 := by
  have h6 : χ ^ 6 = 1 := (orderOf_dvd_iff_pow_eq_one).mp (by rw [hχ])
  rw [probePrimeLocalCOne_eq K p hp χ hminus]
  by_cases hdr : r = d + 1
  · subst r
    rw [ite_eq_left (by omega), ite_eq_left rfl,
      probePrimeResidueTransform_prime_pow K p hp χ hχ,
      ite_eq_left (by omega), probeSextic_power_reduce χ h6 d 5]
    calc
      _ = (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (6 * d + 5) *
          (probePrimeTau K p hp.ne_zero χ * probePrimeTau K p hp.ne_zero (χ ^ 5)) := by ring
      _ = _ := by rw [probePrimeGauss_inverse_pair K p hp χ hχ hminus, ← pow_succ]
  · rw [ite_eq_right hdr]
    split_ifs with hle
    · rw [probePrimeResidueTransform_prime_pow K p hp χ hχ,
        ite_eq_right (by omega), ite_eq_right (by omega), mul_zero]
    · rfl

end

end ArtinMatthews.VaryingKummerAnalytic
