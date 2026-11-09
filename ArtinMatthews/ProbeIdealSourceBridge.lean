module

public import ArtinMatthews.ProbeIdealRawAnalyticFactor
public import ArtinMatthews.ProbeIdealSourceWeight
public import ArtinMatthews.ProbeGoodBadSourceBridge


set_option backward.privateInPublic true
@[expose] public section

/-! A single literal source summand for the good and bad local calculations. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain
open scoped NumberField BigOperators Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem probeIdealRawTerm_eq_source (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (η θ ξ w z : ℂ)
    (e : Bool) (l k m : ℕ) :
    let Q : ℝ := Ideal.absNorm (P.asIdeal)
    probeIdealRawTerm K P χ η θ ((Q : ℂ) ^ (-ξ)) ((Q : ℂ) ^ (-w))
      (ArtinMatthews.probeLocalV Q z) (e, l, k, m) =
      probeIdealSourceTerm K P χ 0 (probeIdealGaussGamma K P χ 2)
        (probeIdealGaussLocalVartheta K P χ η) θ ξ w z (probeBoolFinTwo e) l k m := by
  let Q : ℝ := Ideal.absNorm (P.asIdeal)
  let γ := probeIdealGaussGamma K P χ 2
  let ν := probeIdealGaussLocalVartheta K P χ η
  have hQ : 0 < Q := by
    dsimp [Q]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      P.ne_bot)
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
  rw [← probeIdealSourceWeight_eq_source K P χ 0 γ ν θ ξ w z (probeBoolFinTwo e) l k m]
  change _ = probeIdealSourceWeight K P χ 0 (probeBadFirstParameter Q γ ν θ ξ)
    (probeBadThetaParameter Q ν θ ξ) (ArtinMatthews.probeLocalW Q θ w)
    (ArtinMatthews.probeLocalV Q z) (probeBoolFinTwo e) l k m
  rw [hA, hB]
  unfold probeIdealRawTerm probeIdealSourceWeight probeLocalIndexDegree
  simp only [probeBoolFinTwo_val, zero_add, ArtinMatthews.probeLocalW,
    Complex.ofReal_natCast]
  dsimp only [Q, γ, ν]
  simp only [Complex.ofReal_natCast, pow_add, pow_mul, mul_pow]
  ring

end

end ArtinMatthews.VaryingKummerAnalytic
