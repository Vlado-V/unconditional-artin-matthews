module

public import ArtinMatthews.CubicTheta
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction


set_option backward.privateInPublic true
@[expose] public section

/-! The normalized infinite-cusp limit for the actual ideal theta series. -/
noncomputable section
namespace ArtinMatthews

open scoped MatrixGroups Topology
open Complex UpperHalfPlane Filter

/-- Upper-triangular rational cusp representatives preserve approach to
imaginary infinity, so the actual ideal theta remains zero after weight-one
normalization. No modularity is used. -/
theorem tendsto_heckeTheta_cusp_of_lowerLeft_zero
    (χ : OAI.SevenEighths.HeckeFamily.Character) (γ : SL(2, ℤ)) (hc : γ 1 0 = 0) :
    Tendsto (fun τ : ℍ => heckeTheta χ (γ • τ) /
      ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ))) atImInfty (𝓝 0) := by
  have hγ : Tendsto (fun τ : ℍ => γ • τ) atImInfty atImInfty := by
    change Tendsto (fun τ : ℍ => (Matrix.SpecialLinearGroup.mapGL ℝ γ) • τ)
      atImInfty atImInfty
    apply UpperHalfPlane.tendsto_smul_atImInfty
    change (algebraMap ℤ ℝ (γ 1 0)) = 0
    simp [hc]
  have hzero : Tendsto (heckeTheta χ) atImInfty (𝓝 0) := heckeTheta_zeroAtInfty χ
  have h := (hzero.comp hγ).div_const (γ 1 1 : ℂ)
  simpa only [Function.comp_def, hc, Int.cast_zero, zero_mul, zero_add, zero_div] using h

end ArtinMatthews
