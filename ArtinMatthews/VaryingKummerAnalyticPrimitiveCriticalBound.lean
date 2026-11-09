module

public import ArtinMatthews.VaryingKummerAnalyticConductorConvexity


set_option backward.privateInPublic true
@[expose] public section

/-! An actual conductor-uniform critical-line bound. The field discriminant
and signature stay in the field constant; the genuine ideal-conductor exponent
is `3/8`. The same polynomial bound holds throughout Re(s)>=1/2. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex
open scoped NumberField nonZeroDivisors Classical
noncomputable section

theorem mixedConductorScale_integral_three_quarters
    (K : Type*) [Field K] [NumberField K] {M : Ideal (𝓞 K)} (hM : M ≠ ⊥) :
    (mixedConductorScale K (integralIdealFractionalUnit M hM))^(3/4 : ℝ) =
      (mixedDiscriminantScale K)^(3/4 : ℝ)*(Ideal.absNorm M : ℝ)^(3/8 : ℝ) := by
  rw [mixedConductorScale,Real.mul_rpow (mixedDiscriminantScale_pos K).le (Real.sqrt_nonneg _)]
  simp only [integralIdealFractionalUnit,Units.val_mk0,FractionalIdeal.coeIdeal_absNorm,Rat.cast_natCast]
  rw [Real.sqrt_eq_rpow,← Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num

theorem positive_rpow_le_max {A r R : ℝ} (hA : 0 < A) (hr : 0 ≤ r) (hrR : r ≤ R) :
    A^r ≤ max 1 (A^R) := by
  by_cases hA1 : 1 ≤ A
  · exact (Real.rpow_le_rpow_of_exponent_le hA1 hrR).trans (le_max_right _ _)
  · exact (Real.rpow_le_one hA.le (le_of_lt (lt_of_not_ge hA1)) hr).trans (le_max_left _ _)

theorem exists_primitiveContinued_halfplane_polynomial_bound
    (K : Type*) [Field K] [NumberField K] :
    ∃ (C : ℝ) (m : ℕ), 0 < C ∧
      ∀ {M : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
        (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
        (_hnp : ψ.IsNonprincipal) (s : ℂ), (1/2 : ℝ) ≤ s.re →
        ‖ψ.primitiveContinued hM hprim s‖ ≤ C*(Ideal.absNorm M : ℝ)^(3/8 : ℝ)*(|s.im|+2)^m := by
  obtain ⟨C,m,hC,hbound⟩ := exists_primitiveContinued_conductor_convexity K
  let B := max 1 ((mixedDiscriminantScale K)^(3/4 : ℝ))
  have hB : 1 ≤ B := le_max_left _ _
  have hR := primitiveReciprocalBound_pos K
  refine ⟨(C+primitiveReciprocalBound K)*B,m,mul_pos (add_pos hC hR) (zero_lt_one.trans_le hB),?_⟩
  intro M ψ hM hprim hnp s hs
  have hN : 1 ≤ (Ideal.absNorm M : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hM)
  have hNp : 1 ≤ (Ideal.absNorm M : ℝ)^(3/8 : ℝ) := Real.one_le_rpow hN (by norm_num)
  have hh : 1 ≤ (|s.im|+2)^m := one_le_pow₀ (by linarith [abs_nonneg s.im])
  have hmax : max 1 ((mixedConductorScale K (integralIdealFractionalUnit M hM))^(3/4 : ℝ)) ≤
      B*(Ideal.absNorm M : ℝ)^(3/8 : ℝ) := by
    rw [mixedConductorScale_integral_three_quarters K hM]
    apply max_le
    · exact one_le_mul_of_one_le_of_one_le hB hNp
    · exact mul_le_mul_of_nonneg_right (le_max_right 1 _) (Real.rpow_nonneg (zero_le_one.trans hN) _)
  by_cases hs' : s.re ≤ 5/4
  · have H := hbound ψ hM hprim hnp s (by linarith) hs'
    have hpow := (positive_rpow_le_max (mixedConductorScale_pos K (integralIdealFractionalUnit M hM))
      (show (0 : ℝ) ≤ 5/4-s.re by linarith) (show 5/4-s.re ≤ (3/4 : ℝ) by linarith)).trans hmax
    calc
      _ ≤ C*((mixedConductorScale K (integralIdealFractionalUnit M hM))^(5/4-s.re))*(|s.im|+2)^m := H
      _ ≤ C*(B*(Ideal.absNorm M : ℝ)^(3/8 : ℝ))*(|s.im|+2)^m := by gcongr
      _ ≤ _ := by
        have hCB : C ≤ C+primitiveReciprocalBound K := le_add_of_nonneg_right hR.le
        have hp : 0 ≤ B*(Ideal.absNorm M : ℝ)^(3/8 : ℝ)*(|s.im|+2)^m :=
          mul_nonneg (mul_nonneg (zero_le_one.trans hB)
            (Real.rpow_nonneg (zero_le_one.trans hN) (3/8 : ℝ))) (by positivity)
        have H' := mul_le_mul_of_nonneg_right hCB hp
        convert H' using 1 <;> ring
  · have H := ψ.primitiveContinued_norm_le_right hM hprim hnp (by linarith : 5/4 ≤ s.re)
    apply H.trans
    have hbase : primitiveReciprocalBound K ≤ (C+primitiveReciprocalBound K)*B := by nlinarith
    exact hbase.trans ((le_mul_of_one_le_right (by positivity) hNp).trans
      (le_mul_of_one_le_right (by positivity) hh))

end
end ArtinMatthews.VaryingKummerAnalytic
