module

public import ArtinMatthews.SpectralCuspGraphIntegrability
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper


set_option backward.privateInPublic true
@[expose] public section

/-! The elementary two-dimensional compact-support Sobolev estimate. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff
namespace ArtinMatthews

def spectralPlaneDx (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := fderiv ℝ F p (1,0)
def spectralPlaneDy (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := fderiv ℝ F p (0,1)

theorem spectralPlaneDx_smooth {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (spectralPlaneDx F) :=
  (hF.fderiv_right (by simp)).clm_apply contDiff_const

theorem spectralPlaneDy_smooth {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (spectralPlaneDy F) :=
  (hF.fderiv_right (by simp)).clm_apply contDiff_const

theorem spectralPlaneDx_compact {F : ℝ × ℝ → ℝ} (hF : HasCompactSupport F) :
    HasCompactSupport (spectralPlaneDx F) :=
  hF.fderiv_apply ℝ (1,0)

theorem spectralPlaneDy_compact {F : ℝ × ℝ → ℝ} (hF : HasCompactSupport F) :
    HasCompactSupport (spectralPlaneDy F) :=
  hF.fderiv_apply ℝ (0,1)

private theorem plane_sliceX_compact {F : ℝ × ℝ → ℝ} (hF : HasCompactSupport F) (y : ℝ) :
    HasCompactSupport (fun x => F (x,y)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hF.image continuous_fst)
  intro x hx
  exact ⟨(x,y),subset_tsupport F hx,rfl⟩

private theorem plane_sliceY_compact {F : ℝ × ℝ → ℝ} (hF : HasCompactSupport F) (x : ℝ) :
    HasCompactSupport (fun y => F (x,y)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hF.image continuous_snd)
  intro y hy
  exact ⟨(x,y),subset_tsupport F hy,rfl⟩

theorem spectralPlane_pointwise_le_mixed_integral
    {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F) (p : ℝ × ℝ) :
    ‖F p‖ ≤ ∫ q : ℝ × ℝ, ‖spectralPlaneDy (spectralPlaneDx F) q‖ := by
  let G := spectralPlaneDx F
  let H := spectralPlaneDy G
  have hG : ContDiff ℝ ∞ G := spectralPlaneDx_smooth hF
  have hH : ContDiff ℝ ∞ H := spectralPlaneDy_smooth hG
  have hcG : HasCompactSupport G := spectralPlaneDx_compact hcF
  have hcH : HasCompactSupport H := spectralPlaneDy_compact hcG
  have hHI : Integrable H := hH.continuous.integrable_of_hasCompactSupport hcH
  have hdx (x y : ℝ) : deriv (fun t => F (t,y)) x = G (x,y) := by
    exact (hF.differentiable (by simp) (x,y)).hasFDerivAt.comp_hasDerivAt x
      ((hasDerivAt_id x).prodMk (hasDerivAt_const x y)) |>.deriv
  have hdy (x y : ℝ) : deriv (fun t => G (x,t)) y = H (x,y) := by
    exact (hG.differentiable (by simp) (x,y)).hasFDerivAt.comp_hasDerivAt y
      ((hasDerivAt_const y x).prodMk (hasDerivAt_id y)) |>.deriv
  have hFx : (∫ x in Iic p.1, G (x,p.2)) = F p := by
    simpa only [Function.comp_def,id_eq,hdx,Prod.mk.eta] using HasCompactSupport.integral_Iic_deriv_eq
      ((hF.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp))
      (plane_sliceX_compact hcF p.2) p.1
  have hGy (x : ℝ) : (∫ y in Iic p.2, H (x,y)) = G (x,p.2) := by
    simpa only [Function.comp_def,id_eq,hdy] using HasCompactSupport.integral_Iic_deriv_eq
      ((hG.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp))
      (plane_sliceY_compact hcG x) p.2
  have hpoint (x : ℝ) : ‖G (x,p.2)‖ ≤ ∫ y, ‖H (x,y)‖ := by
    rw [← hGy x]
    apply (norm_integral_le_integral_norm _).trans
    exact integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall fun _ => norm_nonneg _) (hH.continuous.comp
        (continuous_const.prodMk continuous_id) |>.integrable_of_hasCompactSupport
          (plane_sliceY_compact hcH x)).norm
  have hGI : Integrable (fun x => ‖G (x,p.2)‖) :=
    (hG.continuous.comp (continuous_id.prodMk continuous_const) |>.integrable_of_hasCompactSupport
      (plane_sliceX_compact hcG p.2)).norm
  have hII : Integrable (fun x => ∫ y, ‖H (x,y)‖) := hHI.norm.integral_prod_left
  calc
    ‖F p‖ = ‖∫ x in Iic p.1, G (x,p.2)‖ := congrArg norm hFx.symm
    _ ≤ ∫ x in Iic p.1, ‖G (x,p.2)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in Iic p.1, ∫ y, ‖H (x,y)‖ :=
      integral_mono hGI.integrableOn hII.integrableOn hpoint
    _ ≤ ∫ x, ∫ y, ‖H (x,y)‖ := integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall fun _ => integral_nonneg fun _ => norm_nonneg _) hII
    _ = ∫ q : ℝ × ℝ, ‖H q‖ := (integral_prod _ hHI.norm).symm

end ArtinMatthews
