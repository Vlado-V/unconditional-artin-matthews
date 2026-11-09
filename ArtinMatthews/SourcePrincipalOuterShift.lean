module

public import ArtinMatthews.SourcePrincipalContourGeometry
public import OAI.NumberTheory.DirichletL.Detector.Physical


set_option backward.privateInPublic true
@[expose] public section

/-! The remaining principal angular contour moves to the literal line two. -/

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain Set MeasureTheory
open VaryingKummerAnalytic QuadraticWeil SourcePhysical
open OAI.SevenEighths.Continuation OAI.SevenEighths.ProbePhysical
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
local notation "S" => sourceHilbertSet F S₀
local notation "σ₁" => sourcePrincipalSigma

theorem sourcePrincipalPoissonDoubleKernel_outer_shift
    (hcut : principalAngularCutoff F J ⊆ S) {Z : ℝ} (hZ : 0 < Z) :
    Integrable (fun u : ℝ => sourcePrincipalPoissonDoubleKernel F hζ S₀ η Z (sourcePoissonVertical σ₁ u)) ∧
      verticalIntegral σ₁ (sourcePrincipalPoissonDoubleKernel F hζ S₀ η Z) =
        principalAngularGaussianSignal hζ η S Z := by
  let G (s : ℂ) := principalAngularCorrection hζ η S s * (principalAngularExteriorL η S s)⁻¹
  let K := sourcePrincipalPoissonDoubleKernel F hζ S₀ η Z
  let D : Set ℂ := {s | σ₁ ≤ s.re ∧ s.re ≤ 2}
  have hσ : σ₁ ≤ 2 := by norm_num [sourcePrincipalSigma]
  have hG : DifferentiableOn ℂ G D := by
    intro s hs
    have hs' : 1 < s.re := sourcePrincipalSigma_gt_one.trans_le hs.1
    have hr : 99799 / 100000 < s.re := by linarith
    exact (((principalAngularCorrection_analyticOnNhd hζ η S hcut) s hr).differentiableAt.mul
      (((principalAngularExteriorL_differentiableOn η S s hs').differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs')).inv
        (principalAngularExteriorL_ne_zero η S hs'))).differentiableWithinAt
  have hK : DifferentiableOn ℂ K D := gaussianContourIntegrand_differentiableOn hG (-8 / 15) hZ
  let U (x : ℝ) := Z ^ (x - 8 / 15) * Real.exp ((x - 5 / 6) ^ 2)
  have hU : Continuous U := by
    unfold U
    simp_rw [Real.rpow_def_of_pos hZ]
    fun_prop
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := σ₁) (b := (2 : ℝ))).exists_bound_of_continuousOn hU.continuousOn
  let C := probeGoodProductUniformBound F * (sourceRayAbsoluteEulerBound F σ₁ * (4 : ℝ) ^ (S).card)
  have hC : 0 ≤ C := mul_nonneg (probeGoodProductUniformBound_pos F).le
    (mul_nonneg (sourceRayAbsoluteEulerBound_pos F _).le (by positivity))
  have hbound (x : ℝ) (hx : x ∈ Icc σ₁ 2) (u : ℝ) :
      ‖K (sourcePoissonVertical x u)‖ ≤ (max 0 B * C) * Real.exp (-(u ^ 2)) := by
    let s := sourcePoissonVertical x u
    have hA : ‖G s‖ ≤ C := by
      dsimp only [G, C]
      rw [← sourcePrincipalEulerAmplitude_specialize F hζ S₀ η s]
      apply sourcePrincipalEulerAmplitude_norm_le F hζ S₀ η hcut sourcePrincipalSigma_gt_one
      · simpa only [s, sourcePoissonVertical_re] using hx.1
      · apply interior_subset (probeEulerOpenDomain_subset_interior (Or.inr ?_))
        change 99799 / 100000 < s.re ∧ 94999 / 100000 < ((1 : ℂ)).re ∧
          15999 / 100000 < ((1 / 6 : ℂ)).re
        have hsr : 1 < s.re := by simpa only [s, sourcePoissonVertical_re] using
          sourcePrincipalSigma_gt_one.trans_le hx.1
        exact ⟨by linarith, by norm_num, by norm_num [Complex.div_re]⟩
    have hU' : U x ≤ max 0 B :=
      (le_abs_self _).trans ((by simpa only [Real.norm_eq_abs] using hB x hx : |U x| ≤ B).trans
        (le_max_right _ _))
    change ‖gaussianContourIntegrand G (-8 / 15) Z ((x : ℂ) + u * Complex.I)‖ ≤ _
    rw [norm_gaussianContourIntegrand G (-8 / 15) x u hZ]
    have he : (x + (-8 / 15 : ℝ)) = x - 8 / 15 := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (mul_le_mul hU' hA (norm_nonneg _) (le_max_left _ _))
      (Real.exp_nonneg _)
  have hi : Integrable (fun u : ℝ => K (sourcePoissonVertical σ₁ u)) := by
    have hc : Continuous (fun u : ℝ => K (sourcePoissonVertical σ₁ u)) :=
      hK.continuousOn.comp_continuous (sourcePoissonVertical_continuous σ₁)
        (fun _ => by simp only [D, mem_ofPred_eq, sourcePoissonVertical_re, le_rfl, true_and]; exact hσ)
    exact integrable_of_gaussian_bound _ _ hc.aestronglyMeasurable (hbound σ₁ ⟨le_rfl,hσ⟩)
  refine ⟨hi, ?_⟩
  have hs := vertical_integral_eq_of_gaussian_bound K (C := max 0 B * C) hσ hK
    (by simpa only [sourcePoissonVertical] using hbound)
  rw [verticalIntegral, hs, principalAngularGaussianSignal_eq_contour hζ η S hZ]
  simp only [K, sourcePrincipalPoissonDoubleKernel, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_mul, Complex.ofReal_ofNat]

end
end ArtinMatthews.SourceEulerAssembly
