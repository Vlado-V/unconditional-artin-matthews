module

public import ArtinMatthews.QuadraticHeckeCutoffCoefficientBounds


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField VaryingKummerAnalytic UniqueFactorizationMonoid
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]

/-- The omitted-term weight after the quadratic ideal coefficient is separated. -/
def quadraticHeckeCutoffWeight (H : ℝ) (h d e : Ideal (𝓞 K)) : ℂ :=
  if H < (Ideal.absNorm (h * d) : ℝ) then
    -(moebius e : ℂ) / (Real.sqrt (Ideal.absNorm (h * d * e) : ℝ) : ℂ) else 0

/-- The half coefficient is the character coefficient divided by the positive real square root. -/
theorem quadraticHeckeHalfCoefficient_eq_div_sqrt {M : Ideal (𝓞 K)}
    (ψ : EvenIdealRayCharacter K M) (J : Ideal (𝓞 K)) :
    quadraticHeckeHalfCoefficient K ψ J =
      ψ.allCoefficient J / (Real.sqrt (Ideal.absNorm J : ℝ) : ℂ) := by
  have hp : (Ideal.absNorm J : ℂ) ^ (-(1 / 2 : ℂ)) =
      (Real.sqrt (Ideal.absNorm J : ℝ) : ℂ)⁻¹ := by
    calc
      _ = (((Ideal.absNorm J : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
        convert (Complex.ofReal_cpow (Nat.cast_nonneg (Ideal.absNorm J)) (-(1 / 2 : ℝ))).symm using 1
        push_cast
        rfl
      _ = _ := by rw [Real.rpow_neg (Nat.cast_nonneg _), ← Real.sqrt_eq_rpow, Complex.ofReal_inv]
  rw [quadraticHeckeHalfCoefficient_apply, hp, div_eq_mul_inv]

/-- The exact omitted summand separates into a real-norm weight and the character value. -/
theorem quadraticHeckeCutoffTail_summand {M : Ideal (𝓞 K)}
    (ψ : EvenIdealRayCharacter K M) (H : ℝ) (h d e : Ideal (𝓞 K)) :
    (if H < (Ideal.absNorm (h * d) : ℝ) then
      -(moebius e : ℂ) * quadraticHeckeHalfCoefficient K ψ (h * d * e) else 0) =
        quadraticHeckeCutoffWeight K H h d e * ψ.allCoefficient (h * d * e) := by
  by_cases hc : H < (Ideal.absNorm (h * d) : ℝ)
  · rw [ite_eq_left hc, quadraticHeckeCutoffWeight, ite_eq_left hc,
      quadraticHeckeHalfCoefficient_eq_div_sqrt]
    ring
  · rw [ite_eq_right hc, quadraticHeckeCutoffWeight, ite_eq_right hc, zero_mul]

/-- Every omitted term gains the reciprocal square root of the original cutoff. -/
theorem quadraticHeckeCutoffWeight_norm_le {H : ℝ} (hH : 0 < H)
    (h d e : Ideal (𝓞 K)) (he : e ≠ ⊥) :
    ‖quadraticHeckeCutoffWeight K H h d e‖ ≤ 1 / Real.sqrt H := by
  by_cases hc : H < (Ideal.absNorm (h * d) : ℝ)
  · rw [quadraticHeckeCutoffWeight, ite_eq_left hc, norm_div, norm_neg,
      Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have hn : H < (Ideal.absNorm (h * d * e) : ℝ) :=
      hc.trans_le (quadraticHeckeNorm_le_norm_mul_right K (h * d) he)
    have hroot : 0 < Real.sqrt H := Real.sqrt_pos.mpr hH
    apply (div_le_div_of_nonneg_right (HeckeIdealMobius.norm_moebius_le_one K e)
      (Real.sqrt_nonneg _)).trans
    exact div_le_div_of_nonneg_left zero_le_one hroot (Real.sqrt_le_sqrt hn.le)
  · rw [quadraticHeckeCutoffWeight, ite_eq_right hc, norm_zero]
    positivity

end
end ArtinMatthews
