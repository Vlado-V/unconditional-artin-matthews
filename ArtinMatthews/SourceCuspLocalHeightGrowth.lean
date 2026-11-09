module

public import ArtinMatthews.SourceArchMatrixHeight


set_option backward.privateInPublic true
@[expose] public section

/-! The actual inverse-entry height constant grows polynomially along positive diagonal rays. -/
namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section

theorem sourceKPEntryBound_left_diagonal_inverse (g : GL (Fin 2) ℂ)
    (a : ℂˣ) (ha : 1 ≤ ‖(a : ℂ)‖) :
    sourceKPEntryBound (sourceKPDiagonalHom ℂ a⁻¹ * g) ≤ sourceKPEntryBound g := by
  have hainv : ‖((a⁻¹ : ℂˣ) : ℂ)‖ ≤ 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv]
    exact inv_le_one_of_one_le₀ ha
  have hentry (i j : Fin 2) :
      ‖(sourceKPDiagonalHom ℂ a⁻¹ * g) i j‖ ≤ sourceKPEntryBound g := by
    fin_cases i
    · change ‖(sourceKPDiagonalHom ℂ a⁻¹ * g) 0 j‖ ≤ sourceKPEntryBound g
      have he : (sourceKPDiagonalHom ℂ a⁻¹ * g) 0 j = ((a⁻¹ : ℂˣ) : ℂ) * g 0 j := by
        simp [sourceKPDiagonalHom, Matrix.mul_apply, Fin.sum_univ_two]
      rw [he, norm_mul]
      exact (mul_le_mul_of_nonneg_right hainv (norm_nonneg _)).trans
        (by simpa only [one_mul] using sourceKPEntryBound_entry g 0 j)
    · change ‖(sourceKPDiagonalHom ℂ a⁻¹ * g) 1 j‖ ≤ sourceKPEntryBound g
      have he : (sourceKPDiagonalHom ℂ a⁻¹ * g) 1 j = g 1 j := by
        simp [sourceKPDiagonalHom, Matrix.mul_apply, Fin.sum_univ_two]
      rw [he]
      exact sourceKPEntryBound_entry g 1 j
  exact max_le (sourceKPEntryBound_one_le g)
    (max_le (max_le (hentry 0 0) (hentry 0 1)) (max_le (hentry 1 0) (hentry 1 1)))

theorem sourceArchMatrixHeightConstant_right_diagonal (g : GL (Fin 2) ℂ)
    (a : ℂˣ) (ha : 1 ≤ ‖(a : ℂ)‖) :
    sourceArchMatrixHeightConstant (g * sourceKPDiagonalHom ℂ a) ≤
      ‖(a : ℂ)‖ * sourceArchMatrixHeightConstant g := by
  have hinv : (g * sourceKPDiagonalHom ℂ a)⁻¹ = sourceKPDiagonalHom ℂ a⁻¹ * g⁻¹ := by
    rw [_root_.mul_inv_rev, map_inv]
  have hM : sourceKPEntryBound (g * sourceKPDiagonalHom ℂ a)⁻¹ ≤ sourceKPEntryBound g⁻¹ := by
    rw [hinv]
    exact sourceKPEntryBound_left_diagonal_inverse g⁻¹ a ha
  have hdet : (GeneralLinearGroup.det (sourceKPDiagonalHom ℂ a) : ℂ) = a := by
    simp [sourceKPDiagonalHom, GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  unfold sourceArchMatrixHeightConstant
  rw [map_mul, Units.val_mul, norm_mul, hdet]
  apply max_le
  · have hm : 1 ≤ max 1 (4 * ‖(GeneralLinearGroup.det g : ℂ)‖ * sourceKPEntryBound g⁻¹ ^ 2) :=
      le_max_left _ _
    exact hm.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right ha (le_trans zero_le_one hm))
  · calc
      _ = ‖(a : ℂ)‖ * (4 * ‖(GeneralLinearGroup.det g : ℂ)‖ *
          sourceKPEntryBound (g * sourceKPDiagonalHom ℂ a)⁻¹ ^ 2) := by ring
      _ ≤ ‖(a : ℂ)‖ * (4 * ‖(GeneralLinearGroup.det g : ℂ)‖ * sourceKPEntryBound g⁻¹ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀
          (le_trans zero_le_one (sourceKPEntryBound_one_le _)) hM 2
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _)

end
end ArtinMatthews.SourceArchJacquet
