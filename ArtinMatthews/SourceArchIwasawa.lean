module

public import ArtinMatthews.SourceArchSphericalUnitary


set_option backward.privateInPublic true
@[expose] public section

/-! Explicit complex Gram factorization with the actual unitary group. -/
namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section

def sourceArchRowFrame (g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![star (g 1 1), -star (g 1 0); g 1 0, g 1 1]

theorem sourceArchRowFrame_gram (g : GL (Fin 2) ℂ) :
    sourceArchRowFrame g * star (sourceArchRowFrame g) =
      (sourceArchBottomNorm g : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceArchRowFrame, sourceArchBottomNorm, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.star_apply, Complex.mul_conj', mul_comm]
  ring

def sourceArchRowRadius (g : GL (Fin 2) ℂ) : ℝ := Real.sqrt (sourceArchBottomNorm g)

theorem sourceArchRowRadius_pos (g : GL (Fin 2) ℂ) : 0 < sourceArchRowRadius g :=
  Real.sqrt_pos.mpr (sourceArchBottomNorm_pos g)

theorem sourceArchRowRadius_sq (g : GL (Fin 2) ℂ) :
    sourceArchRowRadius g ^ 2 = sourceArchBottomNorm g :=
  Real.sq_sqrt (sourceArchBottomNorm_pos g).le

def sourceArchIwasawaUnitary (g : GL (Fin 2) ℂ) : Matrix.unitaryGroup (Fin 2) ℂ := by
  let r : ℂ := sourceArchRowRadius g
  have hr : r ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (sourceArchRowRadius_pos g))
  have hrsq : r ^ 2 = (sourceArchBottomNorm g : ℂ) := by
    change (sourceArchRowRadius g : ℂ) ^ 2 = (sourceArchBottomNorm g : ℂ)
    exact_mod_cast sourceArchRowRadius_sq g
  refine ⟨r⁻¹ • sourceArchRowFrame g, Matrix.mem_unitaryGroup_iff.mpr ?_⟩
  rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, sourceArchRowFrame_gram,
    smul_smul, smul_smul]
  have hstar : star r⁻¹ = r⁻¹ := by simp [r]
  rw [hstar, ← hrsq]
  have he : r⁻¹ * r⁻¹ * r ^ 2 = 1 := by field_simp
  rw [he, one_smul]

theorem sourceArchIwasawaUnitary_inv (g : GL (Fin 2) ℂ) :
    (((sourceArchUnitaryGL (sourceArchIwasawaUnitary g))⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      (sourceArchRowRadius g : ℂ)⁻¹ • star (sourceArchRowFrame g) := by
  change star ((sourceArchRowRadius g : ℂ)⁻¹ • sourceArchRowFrame g) = _
  rw [star_smul]
  simp

theorem sourceArchIwasawa_bottom_left (g : GL (Fin 2) ℂ) :
    (g * (sourceArchUnitaryGL (sourceArchIwasawaUnitary g))⁻¹) 1 0 = 0 := by
  change ((g : Matrix (Fin 2) (Fin 2) ℂ) *
    (((sourceArchUnitaryGL (sourceArchIwasawaUnitary g))⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) 1 0 = 0
  rw [sourceArchIwasawaUnitary_inv]
  simp [sourceArchRowFrame, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
  ring

theorem sourceArchIwasawa_bottom_right (g : GL (Fin 2) ℂ) :
    (g * (sourceArchUnitaryGL (sourceArchIwasawaUnitary g))⁻¹) 1 1 = sourceArchRowRadius g := by
  change ((g : Matrix (Fin 2) (Fin 2) ℂ) *
    (((sourceArchUnitaryGL (sourceArchIwasawaUnitary g))⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) 1 1 = _
  rw [sourceArchIwasawaUnitary_inv]
  have hs : (sourceArchBottomNorm g : ℂ) = (sourceArchRowRadius g : ℂ) ^ 2 := by
    exact_mod_cast (sourceArchRowRadius_sq g).symm
  have hr : (sourceArchRowRadius g : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (sourceArchRowRadius_pos g))
  calc
    _ = (g 1 0 * star (g 1 0) + g 1 1 * star (g 1 1)) * (sourceArchRowRadius g : ℂ)⁻¹ := by
      simp [sourceArchRowFrame, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
      ring
    _ = (sourceArchBottomNorm g : ℂ) * (sourceArchRowRadius g : ℂ)⁻¹ := by
      simp [sourceArchBottomNorm, Complex.mul_conj']
    _ = _ := by rw [hs]; field_simp

def sourceArchIwasawaScalar (g : GL (Fin 2) ℂ) : ℂˣ :=
  Units.mk0 (sourceArchRowRadius g : ℂ)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (sourceArchRowRadius_pos g)))

def sourceArchIwasawaBorel (g : GL (Fin 2) ℂ) : GL (Fin 2) ℂ :=
  (g * (sourceArchUnitaryGL (sourceArchIwasawaUnitary g))⁻¹) *
    GeneralLinearGroup.scalar (Fin 2) (sourceArchIwasawaScalar g)⁻¹

theorem sourceArchIwasawaBorel_mem (g : GL (Fin 2) ℂ) :
    sourceArchIwasawaBorel g ∈ sourceGL2NormalizedBorel ℂ := by
  constructor
  · rw [sourceArchIwasawaBorel, sourceKPMatrix_right_scalar_entry,
      sourceArchIwasawa_bottom_left, zero_mul]
  · rw [sourceArchIwasawaBorel, sourceKPMatrix_right_scalar_entry,
      sourceArchIwasawa_bottom_right]
    exact (sourceArchIwasawaScalar g).val_inv

theorem sourceArchIwasawa_factor (g : GL (Fin 2) ℂ) :
    g = sourceArchIwasawaBorel g *
      GeneralLinearGroup.scalar (Fin 2) (sourceArchIwasawaScalar g) *
        sourceArchUnitaryGL (sourceArchIwasawaUnitary g) := by
  simp [sourceArchIwasawaBorel]

theorem sourceArchIwasawa_torus_norm (g : GL (Fin 2) ℂ) :
    ‖(GeneralLinearGroup.det (sourceArchIwasawaBorel g) : ℂ)‖ = sourceArchHeight g := by
  conv_rhs => rw [sourceArchIwasawa_factor g]
  rw [sourceArchHeight_unitary, sourceArchHeight_scalar]
  have hb := sourceArchIwasawaBorel_mem g
  unfold sourceArchHeight sourceArchBottomNorm
  rw [hb.1, hb.2]
  simp

end
end ArtinMatthews.SourceArchJacquet
