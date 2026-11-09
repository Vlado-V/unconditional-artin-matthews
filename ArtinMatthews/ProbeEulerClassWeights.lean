module

public import ArtinMatthews.ProbePrimeSixthTable


set_option backward.privateInPublic true
@[expose] public section

/-! Exact weights of the four surviving local classes.  The phase relation
is isolated in an algebraic helper and discharged by the constructed actual
Gauss correction in the final specialization. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped NumberField Classical
noncomputable section

theorem probe_cycle_weight (q v θ a : ℂ) (hq : q ≠ 0) (hθ : θ ^ 6 = 1) (d : ℕ) :
    v ^ (6 * d) * (θ⁻¹) ^ (6 * d) * (q⁻¹) ^ (2 * d) *
      a ^ (6 * d) * q ^ (6 * d) = (v ^ 6 * q ^ 4 * a ^ 6) ^ d := by
  have hθd : (θ⁻¹) ^ (6 * d) = 1 := by
    rw [pow_mul, inv_pow, hθ, inv_one, one_pow]
  have hqd : (q⁻¹) ^ (2 * d) * q ^ (6 * d) = q ^ (4 * d) := by
    rw [pow_mul, pow_mul, pow_mul, ← mul_pow]
    congr 1
    field_simp
  rw [hθd, mul_one]
  calc
    _ = v ^ (6 * d) * a ^ (6 * d) * ((q⁻¹) ^ (2 * d) * q ^ (6 * d)) := by ring
    _ = _ := by rw [hqd]; simp only [mul_pow, pow_mul]; ring

theorem probe_cycle_weight_principal (q v θ a : ℂ)
    (hq : q ≠ 0) (hθ : θ ^ 6 = 1) (d : ℕ) :
    v ^ (6 * (d + 1)) * (θ⁻¹) ^ (6 * (d + 1)) * (q⁻¹) ^ (2 * (d + 1)) *
      a ^ (6 * (d + 1)) * (q ^ (6 * d + 5) * (q - 1)) =
      (v ^ 6 * q ^ 4 * a ^ 6) ^ (d + 1) * (1 - q⁻¹) := by
  have hqstep : q ^ (6 * d + 5) * (q - 1) =
      q ^ (6 * (d + 1)) * (1 - q⁻¹) := by
    rw [show 6 * (d + 1) = (6 * d + 5) + 1 by omega, pow_succ]
    field_simp
    ring
  rw [hqstep, ← mul_assoc, probe_cycle_weight q v θ a hq hθ]

variable (K : Type*) [Field K] [NumberField K]

theorem probePrimeEuler_phase_scalar (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hchar : ringChar ((𝓞 K) ⧸ Ideal.span {p}) ≠ 2) (η : ℂ) :
    probePrimeGaussGamma K p hp.ne_zero χ 2 *
      probePrimeGaussLocalVartheta K p hp.ne_zero χ η *
      probePrimeTau K p hp.ne_zero χ *
      (Real.sqrt (Ideal.absNorm (Ideal.span {p})) : ℂ)⁻¹ = -η := by
  have h := probePrimeGauss_vartheta_phase K p hp χ hχ hchar η
  rw [probePrimeGaussGamma, pow_one, div_eq_mul_inv] at h
  linear_combination h

def probeEulerZeroClassWeight (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ)
    (v θ a b V : ℂ) (k d r : ℕ) : ℂ :=
  v ^ (6 * (d + 1)) * (θ⁻¹) ^ (6 * (d + 1)) *
    ((Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹) ^ (2 * (d + 1)) *
      a ^ (6 * (d + 1)) * (θ * b) ^ k * V ^ r *
        (if k = 0 then probePrimeLocalCZero K p hp χ (6 * d + 5) (6 * r)
         else probePrimeLocalCOne K p hp χ (6 * d + 5) (6 * r))

def probeEulerOneClassWeight (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ)
    (γ v θ a b V : ℂ) (k d r : ℕ) : ℂ :=
  γ * v ^ (6 * d + 1) * (θ⁻¹) ^ (6 * d + 1) *
    (Real.sqrt (Ideal.absNorm (Ideal.span {p})) : ℂ)⁻¹ *
    ((Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹) ^ (2 * d) *
      a ^ (6 * d + 1) * (θ * b) ^ k * V ^ r *
        (if k = 0 then probePrimeLocalCZero K p hp χ (6 * d) (6 * r)
         else probePrimeLocalCOne K p hp χ (6 * d) (6 * r))

theorem probeEulerZeroClassWeight_zero (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (v θ a b V : ℂ) (hθ : θ ^ 6 = 1) (d r : ℕ) :
    probeEulerZeroClassWeight K p hp.ne_zero χ v θ a b V 0 d r =
      if d < r then
        (v ^ 6 * (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 4 * a ^ 6) ^ (d + 1) *
          (1 - (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹) * V ^ r else 0 := by
  have hq : (Ideal.absNorm (Ideal.span {p}) : ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  unfold probeEulerZeroClassWeight
  rw [ite_eq_left rfl, pow_zero, mul_one, probePrimeLocalCZero_zero_class K p hp χ hχ]
  split_ifs with hdr
  · have hc := probe_cycle_weight_principal (Ideal.absNorm (Ideal.span {p}) : ℂ)
      v θ a hq hθ d
    calc
      _ = (v ^ (6 * (d + 1)) * (θ⁻¹) ^ (6 * (d + 1)) *
          ((Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹) ^ (2 * (d + 1)) *
          a ^ (6 * (d + 1)) *
          ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (6 * d + 5) *
            ((Ideal.absNorm (Ideal.span {p}) : ℂ) - 1))) * V ^ r := by ring
      _ = _ := by rw [hc]
  · ring

theorem probeEulerZeroClassWeight_one (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (v θ a b V : ℂ) (hθ : θ ^ 6 = 1) (d r : ℕ) :
    probeEulerZeroClassWeight K p hp.ne_zero χ v θ a b V 1 d r =
      if r = d + 1 then
        (v ^ 6 * (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 4 * a ^ 6) ^ (d + 1) *
          (θ * b) * V ^ r else 0 := by
  have hq : (Ideal.absNorm (Ideal.span {p}) : ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  unfold probeEulerZeroClassWeight
  rw [ite_eq_right one_ne_zero, pow_one,
    probePrimeLocalCOne_zero_class K p hp χ hχ hminus]
  split_ifs with hdr
  · have hc := probe_cycle_weight (Ideal.absNorm (Ideal.span {p}) : ℂ)
      v θ a hq hθ (d + 1)
    rw [show 6 * d + 6 = 6 * (d + 1) by omega]
    calc
      _ = (v ^ (6 * (d + 1)) * (θ⁻¹) ^ (6 * (d + 1)) *
          ((Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹) ^ (2 * (d + 1)) *
          a ^ (6 * (d + 1)) * (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (6 * (d + 1))) *
          (θ * b) * V ^ r := by ring
      _ = _ := by rw [hc]
  · ring

theorem probeEulerOneClassWeight_zero (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (γ v θ a b V η : ℂ) (hθ : θ ^ 6 = 1)
    (hphase : γ * v * probePrimeTau K p hp.ne_zero χ *
      (Real.sqrt (Ideal.absNorm (Ideal.span {p})) : ℂ)⁻¹ = -η) (d r : ℕ) :
    probeEulerOneClassWeight K p hp.ne_zero χ γ v θ a b V 0 d r =
      if r = d then
        -(η * θ⁻¹ * a) *
          (v ^ 6 * (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 4 * a ^ 6) ^ d * V ^ r else 0 := by
  have hq : (Ideal.absNorm (Ideal.span {p}) : ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  unfold probeEulerOneClassWeight
  rw [ite_eq_left rfl, pow_zero, mul_one, probePrimeLocalCZero_one_class K p hp χ hχ]
  split_ifs with hdr
  · simp only [pow_succ]
    have hc := probe_cycle_weight (Ideal.absNorm (Ideal.span {p}) : ℂ) v θ a hq hθ d
    calc
      _ = (γ * v * probePrimeTau K p hp.ne_zero χ *
          (Real.sqrt (Ideal.absNorm (Ideal.span {p})) : ℂ)⁻¹) * (θ⁻¹ * a) *
          (v ^ (6 * d) * (θ⁻¹) ^ (6 * d) *
            ((Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹) ^ (2 * d) * a ^ (6 * d) *
              (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (6 * d)) * V ^ r := by ring
      _ = _ := by rw [hphase, hc]; ring
  · ring

theorem probeEulerOneClassWeight_one (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (γ v θ a b V η : ℂ) (hθ : θ ^ 6 = 1)
    (hphase : γ * v * probePrimeTau K p hp.ne_zero χ *
      (Real.sqrt (Ideal.absNorm (Ideal.span {p})) : ℂ)⁻¹ = -η) (d r : ℕ) :
    probeEulerOneClassWeight K p hp.ne_zero χ γ v θ a b V 1 d r =
      if d < r then
        -(η * θ⁻¹ * a) * (θ * b) *
          (v ^ 6 * (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 4 * a ^ 6) ^ d *
            ((Ideal.absNorm (Ideal.span {p}) : ℂ) - 1) * V ^ r else 0 := by
  have hq : (Ideal.absNorm (Ideal.span {p}) : ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  unfold probeEulerOneClassWeight
  rw [ite_eq_right one_ne_zero, pow_one,
    probePrimeLocalCOne_one_class K p hp χ hχ hminus]
  split_ifs with hdr
  · simp only [pow_succ]
    have hc := probe_cycle_weight (Ideal.absNorm (Ideal.span {p}) : ℂ) v θ a hq hθ d
    calc
      _ = (γ * v * probePrimeTau K p hp.ne_zero χ *
          (Real.sqrt (Ideal.absNorm (Ideal.span {p})) : ℂ)⁻¹) * (θ⁻¹ * a) * (θ * b) *
          (v ^ (6 * d) * (θ⁻¹) ^ (6 * d) *
            ((Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹) ^ (2 * d) * a ^ (6 * d) *
              (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (6 * d)) *
          ((Ideal.absNorm (Ideal.span {p}) : ℂ) - 1) * V ^ r := by ring
      _ = _ := by rw [hphase, hc]; ring
  · ring

end

end ArtinMatthews.VaryingKummerAnalytic
