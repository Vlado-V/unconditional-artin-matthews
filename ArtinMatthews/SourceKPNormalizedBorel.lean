module

public import ArtinMatthews.SourceKPIntegralGroup
public import ArtinMatthews.SourceFiniteKPRankOneTorus


set_option backward.privateInPublic true
@[expose] public section

/-! The literal normalized Borel matrices with bottom row (0,1).
Their factorization and upper-root multiplier laws are derived in the
actual matrix group. -/

namespace ArtinMatthews
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section
variable (F : Type*) [Field F]

def sourceGL2NormalizedBorel : Subgroup (GL (Fin 2) F) where
  carrier := {g | g 1 0 = 0 ∧ g 1 1 = 1}
  one_mem' := by
    change (1 : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧ (1 : Matrix (Fin 2) (Fin 2) F) 1 1 = 1
    simp
  mul_mem' := by
    intro g h hg hh
    change g 1 0 = 0 ∧ g 1 1 = 1 at hg
    change h 1 0 = 0 ∧ h 1 1 = 1 at hh
    change (g * h) 1 0 = 0 ∧ (g * h) 1 1 = 1
    rw [sourceGL2_bottom_left_mul, sourceGL2_bottom_right_mul, hg.1, hg.2, hh.1, hh.2]
    simp
  inv_mem' := by
    intro g hg
    change g 1 0 = 0 ∧ g 1 1 = 1 at hg
    have hdet : (GeneralLinearGroup.det g : F) = g 0 0 := by
      rw [sourceGL2_det_val, hg.1, hg.2, mul_one, mul_zero, sub_zero]
    have h00 : g 0 0 ≠ 0 := hdet ▸ Units.ne_zero (GeneralLinearGroup.det g)
    change g⁻¹ 1 0 = 0 ∧ g⁻¹ 1 1 = 1
    rw [sourceGL2_inverse_adjugate, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
      Matrix.adjugate_fin_two, hdet]
    simp [hg.1, h00]

theorem sourceGL2NormalizedBorel_bottom (g : GL (Fin 2) F) (hg : g ∈ sourceGL2NormalizedBorel F) :
    g 1 0 = 0 ∧ g 1 1 = 1 := hg

theorem sourceGL2NormalizedBorel_upper (x : F) : sourceGL2Upper x ∈ sourceGL2NormalizedBorel F := by
  change (sourceGL2Upper x) 1 0 = 0 ∧ (sourceGL2Upper x) 1 1 = 1
  simp [sourceGL2Upper]

theorem sourceGL2NormalizedBorel_diagonal (y : Fˣ) : sourceGL2Diagonal y ∈ sourceGL2NormalizedBorel F := by
  change (sourceGL2Diagonal y) 1 0 = 0 ∧ (sourceGL2Diagonal y) 1 1 = 1
  simp [sourceGL2Diagonal]

theorem sourceGL2NormalizedBorel_factor (g : GL (Fin 2) F) (hg : g ∈ sourceGL2NormalizedBorel F) :
    g = sourceGL2Upper (g 0 1) * sourceGL2Diagonal (GeneralLinearGroup.det g) := by
  have h := sourceGL2NormalizedBorel_bottom F g hg
  have hdet : (GeneralLinearGroup.det g : F) = g 0 0 := by
    rw [sourceGL2_det_val, h.1, h.2, mul_one, mul_zero, sub_zero]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceGL2Upper, sourceGL2Diagonal, Matrix.mul_apply, Fin.sum_univ_two, h.1, h.2, hdet]

theorem sourceKubotaX_normalizedBorel (g : GL (Fin 2) F) (hg : g ∈ sourceGL2NormalizedBorel F) :
    sourceKubotaX g = 1 := by
  have h := sourceGL2NormalizedBorel_bottom F g hg
  apply Units.ext
  rw [sourceKubotaX_val_right g h.1, h.2, Units.val_one]

theorem sourceKubotaX_left_upper (x : F) (g : GL (Fin 2) F) :
    sourceKubotaX (sourceGL2Upper x * g) = sourceKubotaX g := by
  have hl : (sourceGL2Upper x * g) 1 0 = g 1 0 := by
    simp [sourceGL2_bottom_left_mul, sourceGL2Upper]
  have hr : (sourceGL2Upper x * g) 1 1 = g 1 1 := by
    simp [sourceGL2_bottom_right_mul, sourceGL2Upper]
  apply Units.ext
  by_cases h : g 1 0 = 0
  · rw [sourceKubotaX_val_right _ (hl.trans h), sourceKubotaX_val_right _ h, hr]
  · rw [sourceKubotaX_val_left _ (hl.symm ▸ h), sourceKubotaX_val_left _ h, hl]

variable {F} {A : Type*} [CommGroup A] (B : Fˣ →* (Fˣ →* A))

theorem sourceKP2Multiplier_left_upper (x : F) (g : GL (Fin 2) F) :
    sourceKP2Multiplier B (sourceGL2Upper x) g = 1 := by
  simp [sourceKP2Multiplier, sourceKubotaX_left_upper, sourceKubotaX_upper, sourceGL2Upper_det]

theorem sourceKP2Multiplier_normalizedBorel (g h : GL (Fin 2) F)
    (hg : g ∈ sourceGL2NormalizedBorel F) (hh : h ∈ sourceGL2NormalizedBorel F) :
    sourceKP2Multiplier B g h = B (GeneralLinearGroup.det g) (GeneralLinearGroup.det h) ^ 2 := by
  simp [sourceKP2Multiplier, sourceKubotaX_normalizedBorel F g hg, sourceKubotaX_normalizedBorel F h hh,
    sourceKubotaX_normalizedBorel F (g * h) ((sourceGL2NormalizedBorel F).mul_mem hg hh)]

end
end ArtinMatthews
