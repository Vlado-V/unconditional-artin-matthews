module

public import ArtinMatthews.SourceKubotaMultipliers


set_option backward.privateInPublic true
@[expose] public section

/-! Actual bottom rows and the determinant identity controlling the
right-generator proof of the Kubota cocycle. All matrix products
are in the genuine rank-two general linear group. -/

namespace ArtinMatthews
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups Classical
noncomputable section
variable {F : Type*} [Field F]

theorem sourceGL2_det_val (g : GL (Fin 2) F) :
    ((GeneralLinearGroup.det g : Fˣ) : F) = g 0 0 * g 1 1 - g 0 1 * g 1 0 :=
  Matrix.det_fin_two (g : Matrix (Fin 2) (Fin 2) F)

theorem sourceGL2_bottom_right_ne_zero (g : GL (Fin 2) F) (h : g 1 0 = 0) : g 1 1 ≠ 0 := by
  intro hh
  exact Units.ne_zero (GeneralLinearGroup.det g) (by rw [sourceGL2_det_val, h, hh, mul_zero, mul_zero, sub_zero])

theorem sourceGL2_bottom_left_ne_zero (g : GL (Fin 2) F) (h : g 1 1 = 0) : g 1 0 ≠ 0 := by
  intro hh
  exact sourceGL2_bottom_right_ne_zero g hh h

theorem sourceKubotaX_val_left (g : GL (Fin 2) F) (h : g 1 0 ≠ 0) :
    ((sourceKubotaX g : Fˣ) : F) = g 1 0 := by
  simp [sourceKubotaX, sourceKubotaBottom, h]

theorem sourceKubotaX_val_right (g : GL (Fin 2) F) (h : g 1 0 = 0) :
    ((sourceKubotaX g : Fˣ) : F) = g 1 1 := by
  simp [sourceKubotaX, sourceKubotaBottom, h]

theorem sourceGL2_bottom_left_mul (g h : GL (Fin 2) F) :
    (g * h) 1 0 = g 1 0 * h 0 0 + g 1 1 * h 1 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sourceGL2_bottom_right_mul (g h : GL (Fin 2) F) :
    (g * h) 1 1 = g 1 0 * h 0 1 + g 1 1 * h 1 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sourceKubota_det_cross (g h : GL (Fin 2) F) :
    g 1 0 * (GeneralLinearGroup.det h : F) =
      (g * h) 1 0 * h 1 1 - (g * h) 1 1 * h 1 0 := by
  rw [sourceGL2_det_val, sourceGL2_bottom_left_mul, sourceGL2_bottom_right_mul]
  ring

theorem sourceKubotaX_mul_left_triangular (g h : GL (Fin 2) F) (hg : g 1 0 = 0) :
    sourceKubotaX (g * h) = sourceKubotaX g * sourceKubotaX h := by
  apply Units.ext
  rw [Units.val_mul, sourceKubotaX_val_right g hg]
  have hl : (g * h) 1 0 = g 1 1 * h 1 0 := by rw [sourceGL2_bottom_left_mul, hg, zero_mul, zero_add]
  by_cases hh : h 1 0 = 0
  · have hz : (g * h) 1 0 = 0 := by rw [hl, hh, mul_zero]
    rw [sourceKubotaX_val_right _ hz, sourceKubotaX_val_right h hh, sourceGL2_bottom_right_mul,
      hg, zero_mul, zero_add]
  · have hz : (g * h) 1 0 ≠ 0 := by rw [hl]; exact mul_ne_zero (sourceGL2_bottom_right_ne_zero g hg) hh
    rw [sourceKubotaX_val_left _ hz, sourceKubotaX_val_left h hh, hl]

theorem sourceGL2_right_upper_bottom_left (g : GL (Fin 2) F) (x : F) :
    (g * sourceGL2Upper x) 1 0 = g 1 0 := by
  simp [sourceGL2_bottom_left_mul, sourceGL2Upper]

theorem sourceGL2_right_upper_bottom_right (g : GL (Fin 2) F) (x : F) :
    (g * sourceGL2Upper x) 1 1 = g 1 0 * x + g 1 1 := by
  simp [sourceGL2_bottom_right_mul, sourceGL2Upper]

theorem sourceKubotaX_right_upper (g : GL (Fin 2) F) (x : F) :
    sourceKubotaX (g * sourceGL2Upper x) = sourceKubotaX g := by
  apply Units.ext
  by_cases hg : g 1 0 = 0
  · have hz : (g * sourceGL2Upper x) 1 0 = 0 := (sourceGL2_right_upper_bottom_left g x).trans hg
    rw [sourceKubotaX_val_right _ hz, sourceKubotaX_val_right g hg, sourceGL2_right_upper_bottom_right,
      hg, zero_mul, zero_add]
  · have hz : (g * sourceGL2Upper x) 1 0 ≠ 0 := (sourceGL2_right_upper_bottom_left g x).symm ▸ hg
    rw [sourceKubotaX_val_left _ hz, sourceKubotaX_val_left g hg, sourceGL2_right_upper_bottom_left]

theorem sourceGL2_right_diagonal_bottom_left (g : GL (Fin 2) F) (u : Fˣ) :
    (g * sourceGL2Diagonal u) 1 0 = g 1 0 * (u : F) := by
  simp [sourceGL2_bottom_left_mul, sourceGL2Diagonal]

theorem sourceGL2_right_diagonal_bottom_right (g : GL (Fin 2) F) (u : Fˣ) :
    (g * sourceGL2Diagonal u) 1 1 = g 1 1 := by
  simp [sourceGL2_bottom_right_mul, sourceGL2Diagonal]

theorem sourceKubotaX_right_diagonal (g : GL (Fin 2) F) (u : Fˣ) :
    sourceKubotaX (g * sourceGL2Diagonal u) =
      if g 1 0 = 0 then sourceKubotaX g else sourceKubotaX g * u := by
  apply Units.ext
  by_cases hg : g 1 0 = 0
  · have hz : (g * sourceGL2Diagonal u) 1 0 = 0 := by rw [sourceGL2_right_diagonal_bottom_left, hg, zero_mul]
    rw [ite_eq_left hg, sourceKubotaX_val_right _ hz, sourceKubotaX_val_right g hg,
      sourceGL2_right_diagonal_bottom_right]
  · have hz : (g * sourceGL2Diagonal u) 1 0 ≠ 0 := by
      rw [sourceGL2_right_diagonal_bottom_left]
      exact mul_ne_zero hg (Units.ne_zero u)
    rw [ite_eq_right hg, Units.val_mul, sourceKubotaX_val_left _ hz, sourceKubotaX_val_left g hg,
      sourceGL2_right_diagonal_bottom_left]

theorem sourceGL2_right_weyl_bottom_left (g : GL (Fin 2) F) :
    (g * (sourceGL2Weyl : GL (Fin 2) F)) 1 0 = g 1 1 := by
  simp [sourceGL2_bottom_left_mul, sourceGL2Weyl]

theorem sourceGL2_right_weyl_bottom_right (g : GL (Fin 2) F) :
    (g * (sourceGL2Weyl : GL (Fin 2) F)) 1 1 = g 1 0 := by
  simp [sourceGL2_bottom_right_mul, sourceGL2Weyl]

theorem sourceKubotaX_right_weyl_of_nonzero (g : GL (Fin 2) F) (h : g 1 1 ≠ 0) :
    ((sourceKubotaX (g * sourceGL2Weyl) : Fˣ) : F) = g 1 1 := by
  have hz : (g * (sourceGL2Weyl : GL (Fin 2) F)) 1 0 ≠ 0 := (sourceGL2_right_weyl_bottom_left g).symm ▸ h
  rw [sourceKubotaX_val_left _ hz, sourceGL2_right_weyl_bottom_left]

theorem sourceKubotaX_right_weyl_of_zero (g : GL (Fin 2) F) (h : g 1 1 = 0) :
    ((sourceKubotaX (g * sourceGL2Weyl) : Fˣ) : F) = g 1 0 := by
  have hz : (g * (sourceGL2Weyl : GL (Fin 2) F)) 1 0 = 0 := (sourceGL2_right_weyl_bottom_left g).trans h
  rw [sourceKubotaX_val_right _ hz, sourceGL2_right_weyl_bottom_right]

end
end ArtinMatthews
