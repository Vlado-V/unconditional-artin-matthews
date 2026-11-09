module

public import ArtinMatthews.PrincipalAngularMellinSignal


set_option backward.privateInPublic true
@[expose] public section

/-! Rightward contour shifts and rapid decay for the literal corrected source
signal. The multiplier is the actual angular Euler correction and the finite
Euler deletion is retained. No continuation through a zero is used. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField MeasureTheory Set Filter Asymptotics Complex
open OAI.SevenEighths.Continuation
open scoped NumberField Classical Topology FourierTransform
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {ζ : K} {M : Ideal (𝓞 K)}

def principalAngularSignalEndpointConstant (K : Type*) [Field K] [NumberField K]
    (S : Finset (ArtinMatthews.ProbePrime K)) (B : ℝ) : ℝ :=
  ‖(1 / (2 * Real.pi) : ℂ)‖ * Real.exp ((B - 5 / 6) ^ 2) *
    (probeGoodProductUniformBound K * (primitiveReciprocalBound K * (4 : ℝ) ^ S.card)) *
      ∫ y : ℝ, Real.exp (-(y ^ 2))

theorem principalAngularSignalEndpointConstant_nonneg
    (S : Finset (ArtinMatthews.ProbePrime K)) (B : ℝ) :
    0 ≤ principalAngularSignalEndpointConstant K S B := by
  unfold principalAngularSignalEndpointConstant
  have hg : 0 ≤ ∫ y : ℝ, Real.exp (-(y ^ 2)) :=
    integral_nonneg (fun _ => (Real.exp_pos _).le)
  have hC := (primitiveReciprocalBound_pos K).le
  have hH := (probeGoodProductUniformBound_pos K).le
  positivity

theorem principalAngularSourceFactor_differentiableOn (hζ : IsPrimitiveRoot ζ 12)
    (η : EvenIdealRayCharacter K M) (S : Finset (ArtinMatthews.ProbePrime K))
    (hS : principalAngularCutoff K M ⊆ S) :
    DifferentiableOn ℂ
      (fun s => principalAngularCorrection hζ η S s * (principalAngularExteriorL η S s)⁻¹)
      {s : ℂ | 1 < s.re} := by
  intro s hs
  have hr : 99799 / 100000 < s.re := by change 1 < s.re at hs; linarith
  exact (((principalAngularCorrection_analyticOnNhd hζ η S hS) s hr).differentiableAt.mul
    (((principalAngularExteriorL_differentiableOn η S s hs).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)).inv
        (principalAngularExteriorL_ne_zero η S hs))).differentiableWithinAt

theorem principalAngularSourceFactor_norm_le (hζ : IsPrimitiveRoot ζ 12)
    (η : EvenIdealRayCharacter K M) (S : Finset (ArtinMatthews.ProbePrime K))
    (hS : principalAngularCutoff K M ⊆ S) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖principalAngularCorrection hζ η S s * (principalAngularExteriorL η S s)⁻¹‖ ≤
      probeGoodProductUniformBound K * (primitiveReciprocalBound K * (4 : ℝ) ^ S.card) := by
  rw [norm_mul]
  exact mul_le_mul (principalAngularCorrection_norm_le hζ η S hS (by linarith))
    (principalAngularExteriorL_inv_norm_le η S hs)
    (norm_nonneg _) (probeGoodProductUniformBound_pos K).le

theorem principalAngularGaussianSignal_contour_shift (hζ : IsPrimitiveRoot ζ 12)
    (η : EvenIdealRayCharacter K M) (S : Finset (ArtinMatthews.ProbePrime K))
    (hS : principalAngularCutoff K M ⊆ S) (B : ℝ) (hB : 2 ≤ B)
    {x : ℝ} (hx : 0 < x) :
    principalAngularGaussianSignal hζ η S x = (1 / (2 * Real.pi) : ℂ) *
      ∫ y : ℝ, gaussianContourIntegrand
        (fun s => principalAngularCorrection hζ η S s * (principalAngularExteriorL η S s)⁻¹)
        (-8 / 15) x ((B : ℂ) + y * I) := by
  rw [principalAngularGaussianSignal_eq_contour hζ η S hx]
  congr 1
  apply vertical_integral_eq_of_gaussian_bound (C :=
    max (x ^ (2 + (-8 / 15 : ℝ))) (x ^ (B + (-8 / 15 : ℝ))) *
      Real.exp ((B - 5 / 6) ^ 2) *
        (probeGoodProductUniformBound K * (primitiveReciprocalBound K * (4 : ℝ) ^ S.card))) _ hB
  · apply gaussianContourIntegrand_differentiableOn _ (-8 / 15) hx
    intro z hz
    have hzr : 1 < z.re := by linarith [hz.1]
    exact ((principalAngularSourceFactor_differentiableOn hζ η S hS z hzr).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hzr)).differentiableWithinAt
  · intro a ha y
    rw [norm_gaussianContourIntegrand _ _ _ _ hx]
    have hxpow : x ^ (a + (-8 / 15 : ℝ)) ≤
        max (x ^ (2 + (-8 / 15 : ℝ))) (x ^ (B + (-8 / 15 : ℝ))) := by
      by_cases hx1 : x ≤ 1
      · exact (Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith [ha.1])).trans
          (le_max_left _ _)
      · exact (Real.rpow_le_rpow_of_exponent_le (le_of_lt (lt_of_not_ge hx1))
          (by linarith [ha.2])).trans (le_max_right _ _)
    have hexp : Real.exp ((a - 5 / 6) ^ 2) ≤ Real.exp ((B - 5 / 6) ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [ha.1, ha.2]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have hmax : 0 ≤ max (x ^ (2 + (-8 / 15 : ℝ))) (x ^ (B + (-8 / 15 : ℝ))) :=
      (Real.rpow_nonneg hx.le _).trans (le_max_left _ _)
    exact mul_le_mul (mul_le_mul hxpow hexp (Real.exp_pos _).le hmax)
      (principalAngularSourceFactor_norm_le hζ η S hS (by simpa using ha.1))
      (norm_nonneg _) (mul_nonneg hmax (Real.exp_pos _).le)

theorem principalAngularGaussianSignal_bound_at_zero (hζ : IsPrimitiveRoot ζ 12)
    (η : EvenIdealRayCharacter K M) (S : Finset (ArtinMatthews.ProbePrime K))
    (hS : principalAngularCutoff K M ⊆ S) (B : ℝ) (hB : 2 ≤ B)
    {x : ℝ} (hx : 0 < x) :
    ‖principalAngularGaussianSignal hζ η S x‖ ≤
      principalAngularSignalEndpointConstant K S B * x ^ (B + (-8 / 15 : ℝ)) := by
  rw [principalAngularGaussianSignal_contour_shift hζ η S hS B hB hx, norm_mul]
  have hg : Integrable (fun y : ℝ => Real.exp (-(y ^ 2))) := by
    simpa using integrable_exp_neg_mul_sq (b := 1) (by norm_num)
  have hint := norm_integral_le_of_norm_le
    (hg.const_mul (x ^ (B + (-8 / 15 : ℝ)) * Real.exp ((B - 5 / 6) ^ 2) *
      (probeGoodProductUniformBound K * (primitiveReciprocalBound K * (4 : ℝ) ^ S.card))))
    (f := fun y : ℝ => gaussianContourIntegrand
      (fun s => principalAngularCorrection hζ η S s * (principalAngularExteriorL η S s)⁻¹)
      (-8 / 15) x ((B : ℂ) + y * I))
    (ae_of_all _ (fun y => by
      rw [norm_gaussianContourIntegrand _ _ _ _ hx]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_left
        (principalAngularSourceFactor_norm_le hζ η S hS (by simpa using hB))
        (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le)))
  have H := mul_le_mul_of_nonneg_left hint (norm_nonneg (1 / (2 * Real.pi) : ℂ))
  rw [integral_const_mul] at H
  convert H using 1
  unfold principalAngularSignalEndpointConstant
  ring

theorem principalAngularGaussianSignal_rapidDecayAtZero (hζ : IsPrimitiveRoot ζ 12)
    (η : EvenIdealRayCharacter K M) (S : Finset (ArtinMatthews.ProbePrime K))
    (hS : principalAngularCutoff K M ⊆ S) :
    RapidDecayAtZero (principalAngularGaussianSignal hζ η S) := by
  intro R
  let B : ℝ := max 2 (R - (-8 / 15 : ℝ))
  apply IsBigO.of_bound (principalAngularSignalEndpointConstant K S B)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    (Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with x hx hx1
  have hpow : x ^ (B + (-8 / 15 : ℝ)) ≤ x ^ R :=
    Real.rpow_le_rpow_of_exponent_ge hx hx1
      (by dsimp [B]; linarith [le_max_right (2 : ℝ) (R - (-8 / 15 : ℝ))])
  have H := (principalAngularGaussianSignal_bound_at_zero hζ η S hS B
    (le_max_left _ _) hx).trans
      (mul_le_mul_of_nonneg_left hpow (principalAngularSignalEndpointConstant_nonneg S B))
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx.le R)] using H

end
end ArtinMatthews.VaryingKummerAnalytic
