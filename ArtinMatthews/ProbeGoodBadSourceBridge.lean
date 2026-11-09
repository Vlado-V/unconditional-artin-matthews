module

public import ArtinMatthews.ProbePrimeRawAnalyticFactor
public import ArtinMatthews.ProbeBadPrimeSourceWeight


set_option backward.privateInPublic true
@[expose] public section

/-! A single literal source summand for the good and bad local calculations. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped NumberField BigOperators Classical
noncomputable section

def probeBoolFinTwo : Bool ≃ Fin 2 where
  toFun e := if e then 1 else 0
  invFun i := i = 1
  left_inv e := by cases e <;> rfl
  right_inv i := by fin_cases i <;> rfl

theorem probeBoolFinTwo_val (e : Bool) : (probeBoolFinTwo e).val = if e then 1 else 0 := by
  cases e <;> rfl

def probeSourceIndexEquiv : (Fin 2 × ℕ × ℕ × ℕ) ≃ ProbeLocalRawIndex where
  toFun i := (probeBoolFinTwo.symm i.1, i.2.2.1, i.2.1, i.2.2.2)
  invFun i := (probeBoolFinTwo i.1, i.2.2.1, i.2.1, i.2.2.2)
  left_inv i := by rcases i with ⟨e, k, l, m⟩; simp
  right_inv i := by rcases i with ⟨e, l, k, m⟩; simp

theorem probe_sqrt_cpow_factor (Q : ℝ) (hQ : 0 < Q) (ξ : ℂ) :
    (Real.sqrt Q : ℂ)⁻¹ * (Q : ℂ) ^ (-ξ) = (Q : ℂ) ^ (-(1 / 2 + ξ)) := by
  have hq : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ.ne'
  have hs : (Real.sqrt Q : ℂ) = (Q : ℂ) ^ ((1 : ℂ) / 2) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hQ.le]
    norm_num
  rw [hs, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hq]
  congr 1
  ring

theorem probe_cube_cpow_factor (q : ℂ) (hq : q ≠ 0) (ξ : ℂ) :
    q⁻¹ * (q ^ (-ξ)) ^ 3 = q ^ (-(1 + 3 * ξ)) := by
  rw [← Complex.cpow_neg_one, ← Complex.cpow_nat_mul q 3 (-ξ),
    ← Complex.cpow_add _ _ hq]
  congr 1
  ring

variable (K : Type*) [Field K] [NumberField K]

theorem probePrimeRawTerm_eq_source (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (η θ ξ w z : ℂ)
    (e : Bool) (l k m : ℕ) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    probePrimeRawTerm K p hp χ η θ ((Q : ℂ) ^ (-ξ)) ((Q : ℂ) ^ (-w))
      (ArtinMatthews.probeLocalV Q z) (e, l, k, m) =
      probeBadPrimeSourceTerm K p hp χ 0 (probePrimeGaussGamma K p hp χ 2)
        (probePrimeGaussLocalVartheta K p hp χ η) θ ξ w z (probeBoolFinTwo e) l k m := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  let γ := probePrimeGaussGamma K p hp χ 2
  let ν := probePrimeGaussLocalVartheta K p hp χ η
  have hQ : 0 < Q := by
    dsimp [Q]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp))
  have hq : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ.ne'
  have hA : probeBadFirstParameter Q γ ν θ ξ =
      γ * ν * θ⁻¹ * ((Real.sqrt Q : ℂ)⁻¹ * (Q : ℂ) ^ (-ξ)) := by
    rw [probe_sqrt_cpow_factor Q hQ ξ]
    rfl
  have hB : probeBadThetaParameter Q ν θ ξ =
      ν ^ 3 * (θ⁻¹) ^ 3 * ((Q : ℂ)⁻¹ * ((Q : ℂ) ^ (-ξ)) ^ 3) := by
    rw [probe_cube_cpow_factor _ hq ξ]
    rfl
  dsimp only
  rw [← probeBadPrimeWeight_eq_source K p hp χ 0 γ ν θ ξ w z (probeBoolFinTwo e) l k m]
  change _ = probeBadPrimeWeight K p hp χ 0 (probeBadFirstParameter Q γ ν θ ξ)
    (probeBadThetaParameter Q ν θ ξ) (ArtinMatthews.probeLocalW Q θ w)
    (ArtinMatthews.probeLocalV Q z) (probeBoolFinTwo e) l k m
  rw [hA, hB]
  unfold probePrimeRawTerm probeBadPrimeWeight probeLocalIndexDegree
  simp only [probeBoolFinTwo_val, zero_add, ArtinMatthews.probeLocalW,
    Complex.ofReal_natCast]
  dsimp only [Q, γ, ν]
  simp only [Complex.ofReal_natCast, pow_add, pow_mul, mul_pow]
  ring

end

end ArtinMatthews.VaryingKummerAnalytic
