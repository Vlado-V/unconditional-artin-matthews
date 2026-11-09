module

public import ArtinMatthews.StandardLocalResidueVolume
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar


set_option backward.privateInPublic true
@[expose] public section

/-! Exact Haar scaling of the actual local balls. The prime modulus is
derived from the real residue count, and the standard self-dual volume
then follows from Fourier inversion, including at ramified places. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain MeasureTheory MeasureTheory.Measure StandardAdelic
open OAI.RepresentationTheory.Weil.Local
open scoped NumberField Classical Pointwise ENNReal
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (P : HeightOneSpectrum (𝓞 K))

def sourceLocalPrimeUnit : (P.adicCompletion K)ˣ := Units.mk0 (localPrime K P) (localPrime_ne_zero K P)

theorem sourceLocalPrimeUnit_zpow_ball (n : ℤ) :
    (sourceLocalPrimeUnit K P) ^ (-n) • sourceLocalBall K P 0 = sourceLocalBall K P n := by
  rw [sourceLocalBall_eq_scaled_zero K P n]
  change ((fun x => (((sourceLocalPrimeUnit K P) ^ (-n) : (P.adicCompletion K)ˣ) :
    P.adicCompletion K) * x) '' sourceLocalBall K P 0) = _
  rw [Units.val_zpow_eq_zpow_val]
  rfl

theorem sourceLocalPrimeUnit_modulus :
    (distribHaarChar (P.adicCompletion K) (sourceLocalPrimeUnit K P) : ℝ) =
      (Ideal.absNorm P.asIdeal : ℝ)⁻¹ := by
  let μ := sourceLocalSelfDual K P
  let : μ.IsAddHaarMeasure := sourceLocalSelfDual_isHaar K P
  have hs : sourceLocalPrimeUnit K P • sourceLocalBall K P 0 = sourceLocalBall K P (-1) := by
    simpa only [neg_neg, zpow_one] using sourceLocalPrimeUnit_zpow_ball K P (-1)
  have h := distribHaarChar_mul μ (sourceLocalPrimeUnit K P) (sourceLocalBall K P 0)
  rw [hs] at h
  have he := congrArg ENNReal.toReal h
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal] at he
  change (distribHaarChar (P.adicCompletion K) (sourceLocalPrimeUnit K P) : ℝ) *
    μ.real (sourceLocalBall K P 0) = μ.real (sourceLocalBall K P (-1)) at he
  rw [sourceLocalPrimeBall_volume K P μ, div_eq_mul_inv,
    mul_comm (μ.real (sourceLocalBall K P 0))] at he
  exact mul_right_cancel₀ (sourceLocalBall_volume_pos K P 0).ne' he

theorem sourceLocalBall_volume_scaling (μ : Measure (P.adicCompletion K)) [μ.IsAddHaarMeasure]
    (n : ℤ) : μ.real (sourceLocalBall K P n) =
      (Ideal.absNorm P.asIdeal : ℝ) ^ n * μ.real (sourceLocalBall K P 0) := by
  let u := sourceLocalPrimeUnit K P
  have h := distribHaarChar_mul μ (u ^ (-n)) (sourceLocalBall K P 0)
  rw [show u ^ (-n) • sourceLocalBall K P 0 = sourceLocalBall K P n from
    sourceLocalPrimeUnit_zpow_ball K P n] at h
  have he := congrArg ENNReal.toReal h
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal] at he
  change (distribHaarChar (P.adicCompletion K) (u ^ (-n)) : ℝ) * μ.real (sourceLocalBall K P 0) = _ at he
  have hu : (distribHaarChar (P.adicCompletion K) (u ^ (-n)) : ℝ) = (Ideal.absNorm P.asIdeal : ℝ) ^ n := by
    rw [map_zpow, NNReal.coe_zpow, show (distribHaarChar (P.adicCompletion K) u : ℝ) = _ from
      sourceLocalPrimeUnit_modulus K P, inv_zpow, zpow_neg, inv_inv]
  rw [hu] at he
  exact he.symm

theorem sourceLocalNorm_pos : 0 < (Ideal.absNorm P.asIdeal : ℝ) := by
  exact_mod_cast (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot))

theorem sourceLocalSelfDual_volume_integer :
    (sourceLocalSelfDual K P).real (sourceLocalBall K P 0) =
      (Ideal.absNorm P.asIdeal : ℝ) ^ (-(sourceDifferentExponent K P : ℝ) / 2) := by
  let μ := sourceLocalSelfDual K P
  let : μ.IsAddHaarMeasure := sourceLocalSelfDual_isHaar K P
  let q := (Ideal.absNorm P.asIdeal : ℝ)
  let d := sourceDifferentExponent K P
  let a := μ.real (sourceLocalBall K P 0)
  have hq : 0 < q := sourceLocalNorm_pos K P
  have hp : 0 < q ^ (d : ℤ) := zpow_pos hq _
  have h := sourceLocalSelfDual_volume_product K P
  change a * μ.real (sourceLocalBall K P (d : ℤ)) = 1 at h
  rw [sourceLocalBall_volume_scaling K P μ] at h
  have he : a * a = (q ^ (d : ℤ))⁻¹ := by
    rw [← one_div]
    apply (eq_div_iff hp.ne').mpr
    calc
      a * a * q ^ (d : ℤ) = a * (q ^ (d : ℤ) * a) := by ring
      _ = 1 := h
  calc
    a = Real.sqrt (a * a) := (Real.sqrt_mul_self (sourceLocalBall_volume_pos K P 0).le).symm
    _ = Real.sqrt ((q ^ (d : ℤ))⁻¹) := congrArg Real.sqrt he
    _ = q ^ (-(d : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_eq_inv_rpow, ← Real.rpow_intCast, ← Real.rpow_mul hq.le]
      congr 1
      push_cast
      ring

theorem sourceLocalSelfDual_eq_of_good_volume (μ : Measure (P.adicCompletion K)) [μ.IsAddHaarMeasure]
    (hP : P ∉ traceBadPlaces K) (hμ : μ (sourceLocalBall K P 0) = 1) :
    μ = sourceLocalSelfDual K P := by
  let ν := sourceLocalSelfDual K P
  let : ν.IsAddHaarMeasure := sourceLocalSelfDual_isHaar K P
  have hνf : ν (sourceLocalBall K P 0) ≠ ∞ := (sourceLocalBall_isCompact K P 0).measure_ne_top
  have hν : ν (sourceLocalBall K P 0) = 1 := by
    have h := congrArg ENNReal.ofReal (sourceLocalSelfDual_volume_integer_of_good K P hP)
    change ENNReal.ofReal (ν (sourceLocalBall K P 0)).toReal = ENNReal.ofReal 1 at h
    simpa only [ENNReal.ofReal_toReal hνf, ENNReal.ofReal_one] using h
  let c := addHaarScalarFactor μ ν
  have he : μ = c • ν := isAddLeftInvariant_eq_smul μ ν
  have hc := congrArg (fun m : Measure (P.adicCompletion K) => m (sourceLocalBall K P 0)) he
  change μ (sourceLocalBall K P 0) = (c • ν) (sourceLocalBall K P 0) at hc
  rw [hμ, Measure.coe_nnreal_smul_apply, hν, mul_one] at hc
  have hc' : c = 1 := ENNReal.coe_injective hc.symm
  rw [hc', one_smul] at he
  exact he

end
end ArtinMatthews.SourcePhysical
