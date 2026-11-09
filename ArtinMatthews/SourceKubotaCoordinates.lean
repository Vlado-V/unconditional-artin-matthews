module

public import ArtinMatthews.SourceProjectiveBruhat


set_option backward.privateInPublic true
@[expose] public section

/-! The actual rank-two Kubota coordinates and determinant-modified
multiplier from the source's appendix. This file checks matrix values;
it makes no assertion that the multiplier is a global cocycle. -/

namespace ArtinMatthews
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups Classical
noncomputable section
variable {F : Type*} [Field F]

def sourceKubotaBottom (g : GL (Fin 2) F) : F := if g 1 0 = 0 then g 1 1 else g 1 0

theorem sourceKubotaBottom_ne_zero (g : GL (Fin 2) F) : sourceKubotaBottom g ≠ 0 := by
  unfold sourceKubotaBottom
  split_ifs with h
  · intro h'
    apply GeneralLinearGroup.det_ne_zero g
    simp [Matrix.det_fin_two, h, h']
  · exact h

def sourceKubotaX (g : GL (Fin 2) F) : Fˣ := Units.mk0 (sourceKubotaBottom g) (sourceKubotaBottom_ne_zero g)

def sourceMinusOneUnit (F : Type*) [Field F] : Fˣ := Units.mk0 (-1) (by simp)

def sourceBruhatMiddle (u : Fˣ) : GL (Fin 2) F :=
  sourceGL2Diagonal (sourceBruhatDiagonal u) * GeneralLinearGroup.scalar (Fin 2) u

theorem sourceGL2Weyl_mul_upper_middle (u : Fˣ) :
    sourceGL2Weyl * sourceGL2Upper (u : F) =
      sourceGL2Upper ((u : F)⁻¹) * sourceBruhatMiddle u * sourceGL2Lower ((u : F)⁻¹) := by
  rw [sourceGL2Weyl_mul_upper_scalar, sourceBruhatMiddle, ← mul_assoc
    (sourceGL2Upper ((u : F)⁻¹)) (sourceGL2Diagonal (sourceBruhatDiagonal u)), mul_assoc,
    ← GeneralLinearGroup.scalar_commute u (sourceGL2Lower ((u : F)⁻¹)), ← mul_assoc]

theorem sourceKubotaX_upper (x : F) : sourceKubotaX (sourceGL2Upper x) = 1 := by
  apply Units.ext
  simp [sourceKubotaX, sourceKubotaBottom, sourceGL2Upper]

theorem sourceKubotaX_lower_unit (u : Fˣ) : sourceKubotaX (sourceGL2Lower (u : F)) = u := by
  apply Units.ext
  simp [sourceKubotaX, sourceKubotaBottom, sourceGL2Lower, Units.ne_zero u]

theorem sourceKubotaX_diagonal (u : Fˣ) : sourceKubotaX (sourceGL2Diagonal u) = 1 := by
  apply Units.ext
  simp [sourceKubotaX, sourceKubotaBottom, sourceGL2Diagonal]

theorem sourceKubotaX_weyl : sourceKubotaX (sourceGL2Weyl : GL (Fin 2) F) = 1 := by
  apply Units.ext
  simp [sourceKubotaX, sourceKubotaBottom, sourceGL2Weyl]

theorem sourceKubotaX_upper_diagonal (x : F) (u : Fˣ) :
    sourceKubotaX (sourceGL2Upper x * sourceGL2Diagonal u) = 1 := by
  apply Units.ext
  simp [sourceKubotaX, sourceKubotaBottom, sourceGL2Upper, sourceGL2Diagonal, Matrix.mul_apply, Fin.sum_univ_two]

theorem sourceKubotaX_diagonal_upper (x : F) (u : Fˣ) :
    sourceKubotaX (sourceGL2Diagonal u * sourceGL2Upper x) = 1 := by
  apply Units.ext
  simp [sourceKubotaX, sourceKubotaBottom, sourceGL2Upper, sourceGL2Diagonal, Matrix.mul_apply, Fin.sum_univ_two]

theorem sourceKubotaX_weyl_upper (x : F) :
    sourceKubotaX (sourceGL2Weyl * sourceGL2Upper x) = 1 := by
  apply Units.ext
  simp [sourceKubotaX, sourceKubotaBottom, sourceGL2Weyl, sourceGL2Upper, Matrix.mul_apply, Fin.sum_univ_two]

theorem sourceKubotaX_weyl_diagonal (u : Fˣ) :
    sourceKubotaX (sourceGL2Weyl * sourceGL2Diagonal u) = u := by
  apply Units.ext
  simp [sourceKubotaX, sourceKubotaBottom, sourceGL2Weyl, sourceGL2Diagonal,
    Matrix.mul_apply, Fin.sum_univ_two, Units.ne_zero u]

theorem sourceKubotaX_diagonal_weyl (u : Fˣ) :
    sourceKubotaX (sourceGL2Diagonal u * sourceGL2Weyl) = 1 := by
  apply Units.ext
  simp [sourceKubotaX, sourceKubotaBottom, sourceGL2Weyl, sourceGL2Diagonal, Matrix.mul_apply, Fin.sum_univ_two]

theorem sourceKubotaX_mul_scalar (g : GL (Fin 2) F) (u : Fˣ) :
    sourceKubotaX (g * GeneralLinearGroup.scalar (Fin 2) u) = sourceKubotaX g * u := by
  apply Units.ext
  by_cases h : g 1 0 = 0
  · simp [sourceKubotaX, sourceKubotaBottom, GeneralLinearGroup.coe_scalar,
      Matrix.mul_apply, Matrix.diagonal_apply, h]
  · simp [sourceKubotaX, sourceKubotaBottom, GeneralLinearGroup.coe_scalar,
      Matrix.mul_apply, Matrix.diagonal_apply, h, Units.ne_zero u]

theorem sourceKubotaX_middle (u : Fˣ) : sourceKubotaX (sourceBruhatMiddle u) = u := by
  rw [sourceBruhatMiddle, sourceKubotaX_mul_scalar, sourceKubotaX_diagonal, one_mul]

theorem sourceKubotaX_upper_middle (x : F) (u : Fˣ) :
    sourceKubotaX (sourceGL2Upper x * sourceBruhatMiddle u) = u := by
  rw [sourceBruhatMiddle, ← mul_assoc, sourceKubotaX_mul_scalar, sourceKubotaX_upper_diagonal, one_mul]

theorem sourceGL2Upper_det (x : F) : GeneralLinearGroup.det (sourceGL2Upper x) = 1 := by
  apply Units.ext
  simp [sourceGL2Upper, Matrix.det_fin_two]

theorem sourceGL2Lower_det (x : F) : GeneralLinearGroup.det (sourceGL2Lower x) = 1 := by
  apply Units.ext
  simp [sourceGL2Lower, Matrix.det_fin_two]

theorem sourceGL2Diagonal_det (u : Fˣ) : GeneralLinearGroup.det (sourceGL2Diagonal u) = u := by
  apply Units.ext
  simp [sourceGL2Diagonal, Matrix.det_fin_two]

theorem sourceGL2Weyl_det : GeneralLinearGroup.det (sourceGL2Weyl : GL (Fin 2) F) = sourceMinusOneUnit F := by
  apply Units.ext
  simp [sourceGL2Weyl, sourceMinusOneUnit, Matrix.det_fin_two]

theorem sourceBruhatMiddle_det (u : Fˣ) : GeneralLinearGroup.det (sourceBruhatMiddle u) = sourceMinusOneUnit F := by
  rw [sourceBruhatMiddle, map_mul, sourceGL2Diagonal_det, GeneralLinearGroup.det_scalar]
  apply Units.ext
  simp [sourceBruhatDiagonal, sourceMinusOneUnit]

def sourceKP2Multiplier {A : Type*} [CommGroup A] (B : Fˣ →* (Fˣ →* A))
    (g h : GL (Fin 2) F) : A :=
  B (sourceKubotaX (g * h) / sourceKubotaX g)
    (sourceKubotaX (g * h) / (sourceKubotaX h * GeneralLinearGroup.det g)) *
      B (GeneralLinearGroup.det g) (GeneralLinearGroup.det h) ^ 2

end
end ArtinMatthews
