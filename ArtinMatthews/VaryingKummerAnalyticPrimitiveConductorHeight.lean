module

public import ArtinMatthews.VaryingKummerAnalyticMixedConductorNormalization
public import ArtinMatthews.VaryingKummerAnalyticRayCharacter


set_option backward.privateInPublic true
@[expose] public section

/-! Explicit degree/discriminant/conductor dependence of the genuine
completion scale. No constant here depends on the ideal class choices. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)

theorem mixedConductorScale_integral_log :
    Real.log (mixedConductorScale K (integralIdealFractionalUnit M hM)) =
      Real.log |(discr K:ℝ)|/2 + Real.log (Ideal.absNorm M:ℝ)/2 -
        (InfinitePlace.nrComplexPlaces K:ℝ)*Real.log 2 := by
  have hN := fractionalIdeal_absNorm_pos (integralIdealFractionalUnit (K := K) M hM)
  rw [mixedConductorScale,Real.log_mul (mixedDiscriminantScale_pos K).ne'
    (Real.sqrt_pos.mpr hN).ne',Real.log_sqrt hN.le,mixedDiscriminantScale_log]
  simp only [integralIdealFractionalUnit,Units.val_mk0,FractionalIdeal.coeIdeal_absNorm,
    Rat.cast_natCast]
  ring

theorem mixedConductorScale_integral_log_abs_le :
    |Real.log (mixedConductorScale K (integralIdealFractionalUnit M hM))| ≤
      Real.log |(discr K:ℝ)|/2 + Real.log (Ideal.absNorm M:ℝ)/2 +
        (Module.finrank ℚ K:ℝ)*Real.log 2 := by
  have hD : 0 ≤ Real.log |(discr K:ℝ)| := by
    apply Real.log_nonneg
    exact_mod_cast Int.one_le_abs (discr_ne_zero K)
  have hM0 : Ideal.absNorm M ≠ 0 := fun h => hM (Ideal.absNorm_eq_zero_iff.mp h)
  have hN : 0 ≤ Real.log (Ideal.absNorm M:ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hM0
  have htwo : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  have hn : (InfinitePlace.nrComplexPlaces K:ℝ) ≤ Module.finrank ℚ K := by
    exact_mod_cast (show InfinitePlace.nrComplexPlaces K ≤ Module.finrank ℚ K by
      have H := InfinitePlace.card_add_two_mul_card_eq_rank K
      omega)
  rw [mixedConductorScale_integral_log]
  apply (abs_sub _ _).trans
  rw [abs_of_nonneg (by positivity : 0 ≤ Real.log |(discr K:ℝ)|/2 + Real.log (Ideal.absNorm M:ℝ)/2),
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) htwo)]
  gcongr

end
end ArtinMatthews.VaryingKummerAnalytic
