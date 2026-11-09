module

public import ArtinMatthews.SourceArchScatteringGram
public import ArtinMatthews.SourceArchScatteringKernel


set_option backward.privateInPublic true
@[expose] public section

/-! Exact affine normalization of the spherical kernel at every
matrix in the actual complex projective group. -/
namespace ArtinMatthews.SourceArchJacquet

open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section

def sourceArchAffineCoordinate (g : GL (Fin 2) ℂ) (x : ℂ) : ℂ :=
  (x + sourceArchGramShift g) / (sourceArchHeight g : ℂ)

theorem sourceArchHeight_affine (g : GL (Fin 2) ℂ) (x : ℂ) :
    sourceArchHeight (sourceGL2Weyl * sourceGL2Upper x * g) =
      (sourceArchHeight g)⁻¹ * (1 + ‖sourceArchAffineCoordinate g x‖ ^ 2)⁻¹ := by
  have hH := sourceArchHeight_pos g
  have hden : 0 < ‖x + sourceArchGramShift g‖ ^ 2 + (sourceArchHeight g) ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hH)
  rw [sourceArchHeight_translated, sourceArchAffineCoordinate, norm_div, Complex.norm_real,
    Real.norm_of_nonneg hH.le, div_pow]
  field_simp [hH.ne', hden.ne']
  ring

theorem sourceArchSphericalGL_affine (s : ℂ) (g : GL (Fin 2) ℂ) (x : ℂ) :
    sourceArchSphericalGL s (sourceGL2Weyl * sourceGL2Upper x * g) =
      (sourceArchHeight g : ℂ) ^ (-(2 * s + 1)) *
        sourceArchScatteringKernel s (sourceArchAffineCoordinate g x) := by
  have hH := sourceArchHeight_pos g
  have hq : 0 < 1 + ‖sourceArchAffineCoordinate g x‖ ^ 2 := by positivity
  rw [sourceArchSphericalGL, sourceArchHeight_affine, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (inv_nonneg.mpr hH.le) (inv_nonneg.mpr hq.le),
    Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hH.le, ← Complex.cpow_neg,
    Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hq.le, ← Complex.cpow_neg]
  rfl

theorem sourceArchSphericalSection_translated (s : ℂ) (g : GL (Fin 2) ℂ) (x : ℂ) :
    sourceArchSphericalSection s (sourcePGL2Weyl * sourcePGL2Upper x * ProjGenLinGroup.mk g) =
      (sourceArchHeight g : ℂ) ^ (-(2 * s + 1)) *
        sourceArchScatteringKernel s (sourceArchAffineCoordinate g x) := by
  rw [← map_mul, ← map_mul, sourceArchSphericalSection_mk]
  exact sourceArchSphericalGL_affine s g x

end
end ArtinMatthews.SourceArchJacquet
