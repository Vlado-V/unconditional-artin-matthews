module

public import ArtinMatthews.ProbeBadPrimeCoefficientBounds
public import Mathlib.Analysis.Normed.Ring.InfiniteSum


set_option backward.privateInPublic true
@[expose] public section

/-! The literal bad-prime weights and their genuine coefficient bounds.
The four geometric parameters retain the original local unit phases. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped NumberField Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem probePrimeGaussGamma_norm_one (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (j : ℕ) (hj : 0 < j) (hj6 : j < 6) :
    ‖probePrimeGaussGamma K p hp.ne_zero χ j‖ = 1 := by
  have hn : χ ^ j ≠ 1 := by
    intro he
    have hd := (orderOf_dvd_iff_pow_eq_one).mpr he
    rw [hχ] at hd
    exact (Nat.not_le_of_gt hj6) (Nat.le_of_dvd hj hd)
  have hQ : 0 < (Ideal.absNorm (Ideal.span {p}) : ℝ) :=
    lt_of_lt_of_le zero_lt_one (probePrimeNorm_one_le K p hp.ne_zero)
  rw [probePrimeGaussGamma, norm_div, probePrimeTau_norm K p hp (χ ^ j) hn,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_self (Real.sqrt_pos.mpr hQ).ne'

theorem probePrimeGaussLocalVartheta_norm (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hchar : ringChar ((𝓞 K) ⧸ Ideal.span {p}) ≠ 2) (η : ℂ) :
    ‖probePrimeGaussLocalVartheta K p hp.ne_zero χ η‖ = ‖η‖ := by
  let : (Ideal.span {p} : Ideal (𝓞 K)).IsMaximal :=
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp).isMaximal
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  let : Field ((𝓞 K) ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite ((𝓞 K) ⧸ Ideal.span {p}) :=
    Ring.HasFiniteQuotients.finiteQuotient (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  let : Fintype ((𝓞 K) ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hq : Fintype.card ((𝓞 K) ⧸ Ideal.span {p}) = Ideal.absNorm (Ideal.span {p}) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hγ (j : ℕ) : probePrimeGaussGamma K p hp.ne_zero χ j =
      probeGaussGamma χ (probePrimePhase K p hp.ne_zero) j := by
    simp only [probePrimeGaussGamma, probePrimeTau, tsum_fintype,
      probeGaussGamma, OAI.SevenEighths.ProbeGauss.normalizedGauss, gaussSum, hq]
  have hu := probeSexticGauss_local_unitary χ hχ (probePrimePhase K p hp.ne_zero)
    (probePrimePhase_primitive K p hp.ne_zero) hchar
  have hl : ‖probePrimeGaussLocalLambda K p hp.ne_zero χ‖ = 1 := by
    simpa only [probePrimeGaussLocalLambda, hγ, probeGaussLocalLambda] using hu.1
  have hg : ‖probePrimeGaussLocalG K p hp.ne_zero χ‖ = 1 := by
    simpa only [probePrimeGaussLocalG, hγ, map_ofNat, probeGaussLocalG] using hu.2
  rw [probePrimeGaussLocalVartheta, norm_mul, norm_mul, norm_star, norm_star, hl, hg,
    one_mul, one_mul]

theorem probePrimeCharacter_unit_norm (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (u : 𝓞 K) (hu : ¬p ∣ u) : ‖χ (Ideal.Quotient.mk _ u)‖ = 1 := by
  let : (Ideal.span {p} : Ideal (𝓞 K)).IsMaximal :=
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp).isMaximal
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  let : Field ((𝓞 K) ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  have hu0 : Ideal.Quotient.mk (Ideal.span {p}) u ≠ 0 := by
    intro hz
    exact hu (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))
  have h6 : χ ^ 6 = 1 := (orderOf_dvd_iff_pow_eq_one).mp (by rw [hχ])
  have hpow : χ (Ideal.Quotient.mk _ u) ^ 6 = 1 := by
    rw [← χ.pow_apply' (by decide : 6 ≠ 0), h6,
      MulChar.one_apply (isUnit_iff_ne_zero.mpr hu0)]
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : 6 ≠ 0)).mp
  rw [← norm_pow, hpow, norm_one]

def probeBadPrimeWeight (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (j : ℕ)
    (a b W V : ℂ) (e : Fin 2) (l k m : ℕ) : ℂ :=
  probePrimeLocalCoefficient K p hp χ (e.val + 3 * l) k (j + 6 * m) *
    a ^ e.val * b ^ l * W ^ k * V ^ m

theorem probeBadPrimeWeight_norm_le (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (a b W V : ℂ) (e k : Fin 2) (l m : ℕ) :
    ‖probeBadPrimeWeight K p hp.ne_zero χ j a b W V e l k.val m‖ ≤
      ((Ideal.absNorm (Ideal.span {p}) : ℝ) * ‖a‖) ^ e.val *
      ((Ideal.absNorm (Ideal.span {p}) : ℝ) ^ 3 * ‖b‖) ^ l *
      (Real.sqrt (Ideal.absNorm (Ideal.span {p}) : ℝ) * ‖W‖) ^ k.val * ‖V‖ ^ m := by
  have hC : ‖probePrimeLocalCoefficient K p hp.ne_zero χ (e.val + 3 * l) k.val (j + 6 * m)‖ ≤
      (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (e.val + 3 * l) *
        Real.sqrt (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ k.val := by
    fin_cases k
    · simpa using probePrimeLocalCoefficient_zero_norm_le K p hp χ hχ _ (j + 6 * m)
    · simpa [mul_comm] using probePrimeLocalCoefficient_one_norm_le K p hp χ hχ hminus _ (j + 6 * m)
  simp only [probeBadPrimeWeight, norm_mul, norm_pow]
  calc
    _ ≤ ((Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (e.val + 3 * l) *
        Real.sqrt (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ k.val) *
        ‖a‖ ^ e.val * ‖b‖ ^ l * ‖W‖ ^ k.val * ‖V‖ ^ m := by gcongr
    _ = _ := by simp only [pow_add, pow_mul, mul_pow]; ring

theorem probeBadPrimeWeight_base (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (j : ℕ) (a b W V : ℂ) (m : ℕ) :
    probeBadPrimeWeight K p hp χ j a b W V 0 0 0 m = V ^ m := by
  simp [probeBadPrimeWeight, probePrimeLocalCoefficient_zero_zero]

theorem probeBadPrimeWeight_zero_outer (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (j : ℕ) (hj : 0 < j)
    (a b W V : ℂ) (k m : ℕ) :
    probeBadPrimeWeight K p hp.ne_zero χ j a b W V 0 0 (k + 1) m = 0 := by
  simp only [probeBadPrimeWeight, Fin.val_zero, mul_zero, zero_add]
  rw [probePrimeLocalCoefficient_zero_bad_outer K p hp χ k _ (by omega)]
  simp

theorem probeBadPrimeWeight_first_zero (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (j : ℕ) (hj : 0 < j) (a b W V : ℂ) (m : ℕ) :
    probeBadPrimeWeight K p hp.ne_zero χ j a b W V 1 0 0 m = 0 := by
  simp only [probeBadPrimeWeight, Fin.val_one, mul_zero, add_zero]
  rw [probePrimeLocalCoefficient_bad_first_zero K p hp χ hχ _ (by omega)]
  simp

theorem probeBadPrimeWeight_higher_zero (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (j : ℕ) (hj : 0 < j)
    (a b W V : ℂ) (e : Fin 2) (l k m : ℕ) :
    probeBadPrimeWeight K p hp.ne_zero χ j a b W V e l (k + 2) m = 0 := by
  unfold probeBadPrimeWeight
  rw [probePrimeLocalCoefficient_bad_higher K p hp χ _ k _ (by omega)]
  simp

end
end ArtinMatthews.VaryingKummerAnalytic
