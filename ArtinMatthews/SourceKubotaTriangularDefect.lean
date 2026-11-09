module

public import ArtinMatthews.SourceKubotaWeylSymbol


set_option backward.privateInPublic true
@[expose] public section

/-! The right-upper, right-diagonal and right-scalar cocycle identities
for the actual rank-two multiplier. The two mixed bottom-row cases
retain the exact determinant or minus-one factor. -/

namespace ArtinMatthews
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups Classical
noncomputable section
variable {F : Type*} [Field F] {A : Type*} [CommGroup A]
    (B : Fˣ →* (Fˣ →* A))

theorem sourceKP2Defect_right_upper (hdiag : ∀ x, B x x = 1)
    (g h : GL (Fin 2) F) (x : F) : sourceKP2Defect B g h (sourceGL2Upper x) = 1 := by
  rw [sourceKP2Defect_formula B hdiag, sourceKubotaX_right_upper h x,
    sourceKubotaX_right_upper (g * h) x]
  have ht : (sourceKubotaX (g * h) * sourceKubotaX h) /
      (sourceKubotaX h * sourceKubotaX (g * h)) = 1 := div_eq_one.mpr (mul_comm _ _)
  rw [ht, map_one, MonoidHom.one_apply]

theorem sourceKP2Defect_right_scalar (hdiag : ∀ x, B x x = 1)
    (g h : GL (Fin 2) F) (u : Fˣ) :
    sourceKP2Defect B g h (GeneralLinearGroup.scalar (Fin 2) u) = 1 := by
  rw [sourceKP2Defect_formula B hdiag, sourceKubotaX_mul_scalar h u, sourceKubotaX_mul_scalar (g * h) u]
  have ht : (sourceKubotaX (g * h) * (sourceKubotaX h * u)) /
      (sourceKubotaX h * (sourceKubotaX (g * h) * u)) = 1 := div_eq_one.mpr (by ac_rfl)
  rw [ht, map_one, MonoidHom.one_apply]

theorem sourceKP2Defect_right_diagonal (hdiag : ∀ x, B x x = 1)
    (hminus : ∀ x, B x (sourceMinusOneUnit F) = 1)
    (g h : GL (Fin 2) F) (u : Fˣ) : sourceKP2Defect B g h (sourceGL2Diagonal u) = 1 := by
  by_cases hg : g 1 0 = 0
  · exact sourceKP2Defect_left_triangular B hdiag g h _ hg
  rw [sourceKP2Defect_formula B hdiag, sourceKubotaX_right_diagonal h u,
    sourceKubotaX_right_diagonal (g * h) u, sourceKubotaX_diagonal, mul_one]
  by_cases hh : h 1 0 = 0
  · by_cases hgh : (g * h) 1 0 = 0
    · rw [ite_eq_left hh, ite_eq_left hgh]
      have ht : (sourceKubotaX (g * h) * sourceKubotaX h) /
          (sourceKubotaX h * sourceKubotaX (g * h)) = 1 := div_eq_one.mpr (mul_comm _ _)
      rw [ht, map_one, MonoidHom.one_apply]
    · have he : sourceKubotaX g * GeneralLinearGroup.det h = sourceKubotaX (g * h) * sourceKubotaX h := by
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, sourceKubotaX_val_left g hg, sourceKubotaX_val_left _ hgh,
          sourceKubotaX_val_right h hh, sourceKubota_det_cross, hh, mul_zero, sub_zero]
      rw [ite_eq_left hh, ite_eq_right hgh, he, hdiag]
  · by_cases hgh : (g * h) 1 0 = 0
    · have he : (sourceKubotaX g * GeneralLinearGroup.det h) /
          (sourceKubotaX h * sourceKubotaX (g * h)) = sourceMinusOneUnit F := by
        apply Units.ext
        change (((sourceKubotaX g * GeneralLinearGroup.det h) /
          (sourceKubotaX h * sourceKubotaX (g * h)) : Fˣ) : F) = -1
        rw [Units.val_div_eq_div_val, Units.val_mul, Units.val_mul, sourceKubotaX_val_left g hg,
          sourceKubotaX_val_left h hh, sourceKubotaX_val_right _ hgh, sourceKubota_det_cross,
          hgh, zero_mul, zero_sub, mul_comm (h 1 0) ((g * h) 1 1), neg_div,
          div_self (mul_ne_zero (sourceGL2_bottom_right_ne_zero _ hgh) hh)]
      rw [ite_eq_right hh, ite_eq_left hgh, he, hminus]
    · rw [ite_eq_right hh, ite_eq_right hgh]
      have ht : (sourceKubotaX (g * h) * (sourceKubotaX h * u)) /
          (sourceKubotaX h * (sourceKubotaX (g * h) * u)) = 1 := div_eq_one.mpr (by ac_rfl)
      rw [ht, map_one, MonoidHom.one_apply]

end
end ArtinMatthews
