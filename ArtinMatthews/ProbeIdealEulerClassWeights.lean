module

public import ArtinMatthews.ProbeEulerClassWeights
public import ArtinMatthews.ProbeIdealSixthTable


set_option backward.privateInPublic true
@[expose] public section

/-! Exact weights of the four surviving local classes.  The phase relation
is isolated in an algebraic helper and discharged by the constructed actual
Gauss correction in the final specialization. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain
open scoped NumberField Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem probeIdealEuler_phase_scalar (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hchar : ringChar ((𝓞 K) ⧸ P.asIdeal) ≠ 2) (η : ℂ) :
    probeIdealGaussGamma K P χ 2 *
      probeIdealGaussLocalVartheta K P χ η *
      probeIdealTau K P χ *
      (Real.sqrt (Ideal.absNorm (P.asIdeal)) : ℂ)⁻¹ = -η := by
  have h := probeIdealGauss_vartheta_phase K P χ hχ hchar η
  rw [probeIdealGaussGamma, pow_one, div_eq_mul_inv] at h
  linear_combination h

def probeIdealEulerZeroClassWeight (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ)
    (v θ a b V : ℂ) (k d r : ℕ) : ℂ :=
  v ^ (6 * (d + 1)) * (θ⁻¹) ^ (6 * (d + 1)) *
    ((Ideal.absNorm (P.asIdeal) : ℂ)⁻¹) ^ (2 * (d + 1)) *
      a ^ (6 * (d + 1)) * (θ * b) ^ k * V ^ r *
        (if k = 0 then probeIdealLocalCZero K P χ (6 * d + 5) (6 * r)
         else probeIdealLocalCOne K P χ (6 * d + 5) (6 * r))

def probeIdealEulerOneClassWeight (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ)
    (γ v θ a b V : ℂ) (k d r : ℕ) : ℂ :=
  γ * v ^ (6 * d + 1) * (θ⁻¹) ^ (6 * d + 1) *
    (Real.sqrt (Ideal.absNorm (P.asIdeal)) : ℂ)⁻¹ *
    ((Ideal.absNorm (P.asIdeal) : ℂ)⁻¹) ^ (2 * d) *
      a ^ (6 * d + 1) * (θ * b) ^ k * V ^ r *
        (if k = 0 then probeIdealLocalCZero K P χ (6 * d) (6 * r)
         else probeIdealLocalCOne K P χ (6 * d) (6 * r))

theorem probeIdealEulerZeroClassWeight_zero (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (v θ a b V : ℂ) (hθ : θ ^ 6 = 1) (d r : ℕ) :
    probeIdealEulerZeroClassWeight K P χ v θ a b V 0 d r =
      if d < r then
        (v ^ 6 * (Ideal.absNorm (P.asIdeal) : ℂ) ^ 4 * a ^ 6) ^ (d + 1) *
          (1 - (Ideal.absNorm (P.asIdeal) : ℂ)⁻¹) * V ^ r else 0 := by
  have hq : (Ideal.absNorm (P.asIdeal) : ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      P.ne_bot
  unfold probeIdealEulerZeroClassWeight
  rw [ite_eq_left rfl, pow_zero, mul_one, probeIdealLocalCZero_zero_class K P χ hχ]
  split_ifs with hdr
  · have hc := probe_cycle_weight_principal (Ideal.absNorm (P.asIdeal) : ℂ)
      v θ a hq hθ d
    calc
      _ = (v ^ (6 * (d + 1)) * (θ⁻¹) ^ (6 * (d + 1)) *
          ((Ideal.absNorm (P.asIdeal) : ℂ)⁻¹) ^ (2 * (d + 1)) *
          a ^ (6 * (d + 1)) *
          ((Ideal.absNorm (P.asIdeal) : ℂ) ^ (6 * d + 5) *
            ((Ideal.absNorm (P.asIdeal) : ℂ) - 1))) * V ^ r := by ring
      _ = _ := by rw [hc]
  · ring

theorem probeIdealEulerZeroClassWeight_one (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (v θ a b V : ℂ) (hθ : θ ^ 6 = 1) (d r : ℕ) :
    probeIdealEulerZeroClassWeight K P χ v θ a b V 1 d r =
      if r = d + 1 then
        (v ^ 6 * (Ideal.absNorm (P.asIdeal) : ℂ) ^ 4 * a ^ 6) ^ (d + 1) *
          (θ * b) * V ^ r else 0 := by
  have hq : (Ideal.absNorm (P.asIdeal) : ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      P.ne_bot
  unfold probeIdealEulerZeroClassWeight
  rw [ite_eq_right one_ne_zero, pow_one,
    probeIdealLocalCOne_zero_class K P χ hχ hminus]
  split_ifs with hdr
  · have hc := probe_cycle_weight (Ideal.absNorm (P.asIdeal) : ℂ)
      v θ a hq hθ (d + 1)
    rw [show 6 * d + 6 = 6 * (d + 1) by omega]
    calc
      _ = (v ^ (6 * (d + 1)) * (θ⁻¹) ^ (6 * (d + 1)) *
          ((Ideal.absNorm (P.asIdeal) : ℂ)⁻¹) ^ (2 * (d + 1)) *
          a ^ (6 * (d + 1)) * (Ideal.absNorm (P.asIdeal) : ℂ) ^ (6 * (d + 1))) *
          (θ * b) * V ^ r := by ring
      _ = _ := by rw [hc]
  · ring

theorem probeIdealEulerOneClassWeight_zero (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (γ v θ a b V η : ℂ) (hθ : θ ^ 6 = 1)
    (hphase : γ * v * probeIdealTau K P χ *
      (Real.sqrt (Ideal.absNorm (P.asIdeal)) : ℂ)⁻¹ = -η) (d r : ℕ) :
    probeIdealEulerOneClassWeight K P χ γ v θ a b V 0 d r =
      if r = d then
        -(η * θ⁻¹ * a) *
          (v ^ 6 * (Ideal.absNorm (P.asIdeal) : ℂ) ^ 4 * a ^ 6) ^ d * V ^ r else 0 := by
  have hq : (Ideal.absNorm (P.asIdeal) : ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      P.ne_bot
  unfold probeIdealEulerOneClassWeight
  rw [ite_eq_left rfl, pow_zero, mul_one, probeIdealLocalCZero_one_class K P χ hχ]
  split_ifs with hdr
  · simp only [pow_succ]
    have hc := probe_cycle_weight (Ideal.absNorm (P.asIdeal) : ℂ) v θ a hq hθ d
    calc
      _ = (γ * v * probeIdealTau K P χ *
          (Real.sqrt (Ideal.absNorm (P.asIdeal)) : ℂ)⁻¹) * (θ⁻¹ * a) *
          (v ^ (6 * d) * (θ⁻¹) ^ (6 * d) *
            ((Ideal.absNorm (P.asIdeal) : ℂ)⁻¹) ^ (2 * d) * a ^ (6 * d) *
              (Ideal.absNorm (P.asIdeal) : ℂ) ^ (6 * d)) * V ^ r := by ring
      _ = _ := by rw [hphase, hc]; ring
  · ring

theorem probeIdealEulerOneClassWeight_one (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (γ v θ a b V η : ℂ) (hθ : θ ^ 6 = 1)
    (hphase : γ * v * probeIdealTau K P χ *
      (Real.sqrt (Ideal.absNorm (P.asIdeal)) : ℂ)⁻¹ = -η) (d r : ℕ) :
    probeIdealEulerOneClassWeight K P χ γ v θ a b V 1 d r =
      if d < r then
        -(η * θ⁻¹ * a) * (θ * b) *
          (v ^ 6 * (Ideal.absNorm (P.asIdeal) : ℂ) ^ 4 * a ^ 6) ^ d *
            ((Ideal.absNorm (P.asIdeal) : ℂ) - 1) * V ^ r else 0 := by
  have hq : (Ideal.absNorm (P.asIdeal) : ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      P.ne_bot
  unfold probeIdealEulerOneClassWeight
  rw [ite_eq_right one_ne_zero, pow_one,
    probeIdealLocalCOne_one_class K P χ hχ hminus]
  split_ifs with hdr
  · simp only [pow_succ]
    have hc := probe_cycle_weight (Ideal.absNorm (P.asIdeal) : ℂ) v θ a hq hθ d
    calc
      _ = (γ * v * probeIdealTau K P χ *
          (Real.sqrt (Ideal.absNorm (P.asIdeal)) : ℂ)⁻¹) * (θ⁻¹ * a) * (θ * b) *
          (v ^ (6 * d) * (θ⁻¹) ^ (6 * d) *
            ((Ideal.absNorm (P.asIdeal) : ℂ)⁻¹) ^ (2 * d) * a ^ (6 * d) *
              (Ideal.absNorm (P.asIdeal) : ℂ) ^ (6 * d)) *
          ((Ideal.absNorm (P.asIdeal) : ℂ) - 1) * V ^ r := by ring
      _ = _ := by rw [hphase, hc]; ring
  · ring

end

end ArtinMatthews.VaryingKummerAnalytic
