module

public import ArtinMatthews.PrincipalAngularGaussian


set_option backward.privateInPublic true
@[expose] public section

/-! The actual absolutely convergent principal Mellin integral on the
line two, with the manuscript exponent C_*(s)=s-8/15. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField MeasureTheory Set Filter Complex
open OAI.SevenEighths.Continuation
open scoped NumberField Classical Topology FourierTransform
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {ζ : K} {M : Ideal (𝓞 K)}

theorem principalAngularGaussianSignal_eq_contour (hζ : IsPrimitiveRoot ζ 12)
    (η : EvenIdealRayCharacter K M) (S : Finset (ArtinMatthews.ProbePrime K))
    {x : ℝ} (hx : 0 < x) :
    principalAngularGaussianSignal hζ η S x = (1 / (2 * Real.pi) : ℂ) *
      ∫ y : ℝ, gaussianContourIntegrand
        (fun s => principalAngularCorrection hζ η S s * (principalAngularExteriorL η S s)⁻¹)
        (-8 / 15) x ((2 : ℂ) + y * I) := by
  unfold principalAngularGaussianSignal mellinInv
  simp only [smul_eq_mul, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_one]
  rw [mul_left_comm, ← integral_const_mul]
  congr 1
  rw [← integral_neg_eq_self]
  apply integral_congr_ae
  filter_upwards [] with y
  unfold gaussianContourIntegrand principalAngularGaussianAmplitude
  have he : -(((-2 : ℝ) : ℂ) + (-y : ℝ) * I) = (2 : ℂ) + y * I := by push_cast; ring
  rw [he, ← mul_assoc, ← Complex.cpow_add]
  · push_cast
    ring_nf
  · exact Complex.ofReal_ne_zero.mpr hx.ne'

theorem principalAngularGaussianContour_integrable (hζ : IsPrimitiveRoot ζ 12)
    (η : EvenIdealRayCharacter K M) (S : Finset (ArtinMatthews.ProbePrime K))
    (hS : principalAngularCutoff K M ⊆ S) {x : ℝ} (hx : 0 < x) :
    Integrable (fun y : ℝ => gaussianContourIntegrand
      (fun s => principalAngularCorrection hζ η S s * (principalAngularExteriorL η S s)⁻¹)
      (-8 / 15) x ((2 : ℂ) + y * I)) := by
  let F := fun s => principalAngularCorrection hζ η S s * (principalAngularExteriorL η S s)⁻¹
  have hF : DifferentiableOn ℂ F {s : ℂ | 1 < s.re} := by
    intro s hs
    change 1 < s.re at hs
    have hr : 99799 / 100000 < s.re := by linarith
    exact (((principalAngularCorrection_analyticOnNhd hζ η S hS) s hr).differentiableAt.mul
      (((principalAngularExteriorL_differentiableOn η S s hs).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)).inv
          (principalAngularExteriorL_ne_zero η S hs))).differentiableWithinAt
  have hc : Continuous (fun y : ℝ => gaussianContourIntegrand F (-8 / 15) x ((2 : ℂ) + y * I)) :=
    (gaussianContourIntegrand_differentiableOn hF (-8 / 15) hx).continuousOn.comp_continuous
      (by fun_prop) (by intro y; norm_num)
  apply integrable_of_gaussian_bound _
    (x ^ (2 - 8 / 15 : ℝ) * Real.exp ((2 - 5 / 6 : ℝ) ^ 2) *
      (probeGoodProductUniformBound K * (primitiveReciprocalBound K * (4 : ℝ) ^ S.card)))
    hc.aestronglyMeasurable
  intro y
  have hn := norm_gaussianContourIntegrand F (-8 / 15) 2 y hx
  norm_num only [Complex.ofReal_ofNat] at hn ⊢
  rw [hn]
  have hb : ‖F ((2 : ℂ) + y * I)‖ ≤
      probeGoodProductUniformBound K * (primitiveReciprocalBound K * (4 : ℝ) ^ S.card) := by
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul (principalAngularCorrection_norm_le hζ η S hS (by norm_num))
      (principalAngularExteriorL_inv_norm_le η S (by norm_num))
      (norm_nonneg _) (probeGoodProductUniformBound_pos K).le
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hb
      (mul_nonneg (Real.rpow_nonneg hx.le (22 / 15)) (Real.exp_pos (49 / 36)).le))
    (Real.exp_pos _).le

end
end ArtinMatthews.VaryingKummerAnalytic
