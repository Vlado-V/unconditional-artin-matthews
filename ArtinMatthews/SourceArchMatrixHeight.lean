module

public import ArtinMatthews.SourceKPLocalMatrixHeight
public import ArtinMatthews.SourceArchSphericalUnitary


set_option backward.privateInPublic true
@[expose] public section

/-! A concrete inverse-entry bound for every complex right translate. -/
namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section

def sourceArchMatrixHeightConstant (g : GL (Fin 2) ℂ) : ℝ :=
  max 1 (4 * ‖(GeneralLinearGroup.det g : ℂ)‖ * sourceKPEntryBound g⁻¹ ^ 2)

theorem sourceArchMatrixHeightConstant_pos (g : GL (Fin 2) ℂ) :
    0 < sourceArchMatrixHeightConstant g := by
  unfold sourceArchMatrixHeightConstant
  positivity

theorem sourceArchBottomMax_sq_le (g : GL (Fin 2) ℂ) :
    sourceKPBottomMax g ^ 2 ≤ sourceArchBottomNorm g := by
  unfold sourceKPBottomMax sourceArchBottomNorm
  by_cases h : ‖g 1 0‖ ≤ ‖g 1 1‖
  · rw [max_eq_right h]
    exact le_add_of_nonneg_left (sq_nonneg _)
  · rw [max_eq_left (le_of_not_ge h)]
    exact le_add_of_nonneg_right (sq_nonneg _)

theorem sourceArchHeight_translate (g : GL (Fin 2) ℂ) (x : ℂ) :
    sourceArchHeight ((sourceGL2Weyl * sourceGL2Upper x) * g) ≤
      sourceArchMatrixHeightConstant g * (max 1 ‖x‖)⁻¹ ^ 2 := by
  let h : GL (Fin 2) ℂ := sourceGL2Weyl * sourceGL2Upper x
  let R := sourceKPBottomMax (h * g)
  let D := sourceArchBottomNorm (h * g)
  let M := sourceKPEntryBound g⁻¹
  let X := max 1 ‖x‖
  have hR : 0 < R := sourceKPBottomMax_pos _
  have hD : 0 < D := sourceArchBottomNorm_pos _
  have hX : 0 < X := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hM : 0 ≤ M := le_trans (by norm_num) (sourceKPEntryBound_one_le _)
  have hb : X ≤ 2 * M * R := by
    simpa only [h, X, M, R, sourceKPBottomMax_weyl_upper] using sourceKPBottomMax_mul_inverse_bound h g
  have hsq : X ^ 2 ≤ 4 * M ^ 2 * R ^ 2 := by
    have hs := (sq_le_sq₀ hX.le (by positivity : 0 ≤ 2 * M * R)).mpr hb
    nlinarith
  have hsqD : X ^ 2 ≤ 4 * M ^ 2 * D :=
    hsq.trans (mul_le_mul_of_nonneg_left (sourceArchBottomMax_sq_le (h * g)) (by positivity))
  have hd : 0 ≤ ‖(GeneralLinearGroup.det g : ℂ)‖ := norm_nonneg _
  have hraw : ‖(GeneralLinearGroup.det g : ℂ)‖ / D ≤
      (4 * ‖(GeneralLinearGroup.det g : ℂ)‖ * M ^ 2) / X ^ 2 := by
    apply (div_le_div_iff₀ hD (sq_pos_of_pos hX)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsqD hd]
  have hdet : ‖(GeneralLinearGroup.det (h * g) : ℂ)‖ = ‖(GeneralLinearGroup.det g : ℂ)‖ := by
    rw [map_mul, Units.val_mul, norm_mul,
      show ‖(GeneralLinearGroup.det h : ℂ)‖ = 1 from sourceKPDetNorm_weyl_upper x, one_mul]
  change ‖(GeneralLinearGroup.det (h * g) : ℂ)‖ / D ≤ _
  rw [hdet, sourceArchMatrixHeightConstant]
  calc
    _ ≤ (4 * ‖(GeneralLinearGroup.det g : ℂ)‖ * M ^ 2) / X ^ 2 := hraw
    _ ≤ max 1 (4 * ‖(GeneralLinearGroup.det g : ℂ)‖ * M ^ 2) / X ^ 2 :=
      div_le_div_of_nonneg_right (le_max_right _ _) (sq_nonneg X)
    _ = _ := by dsimp only [M, X]; rw [div_eq_mul_inv, inv_pow]

end
end ArtinMatthews.SourceArchJacquet
