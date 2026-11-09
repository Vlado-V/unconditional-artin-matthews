module

public import ArtinMatthews.SourceArchScatteringValue
public import ArtinMatthews.SourceArchScatteringAffine
public import ArtinMatthews.SourceArchTranslatedKernel
public import ArtinMatthews.SourceArchSphericalUnitary


set_option backward.privateInPublic true
@[expose] public section

/-! The translated archimedean intertwining integral on the actual
spherical section, at every element of PGL2(C). -/
namespace ArtinMatthews.SourceArchJacquet

open MeasureTheory Matrix Matrix.GeneralLinearGroup
open ArtinMatthews.VaryingKummerAnalytic
open scoped MatrixGroups
noncomputable section

def sourceArchSphericalIntertwiner (s : ℂ) (g : PGL(2, ℂ)) : ℂ :=
  ∫ x : ℂ, sourceArchSphericalSection s (sourcePGL2Weyl * sourcePGL2Upper x * g)
    ∂sourceComplexTraceMeasure

theorem sourceArchSphericalIntertwiner_integrable {s : ℂ} (hs : 0 < s.re) (g : PGL(2, ℂ)) :
    Integrable (fun x : ℂ => sourceArchSphericalSection s
      (sourcePGL2Weyl * sourcePGL2Upper x * g)) sourceComplexTraceMeasure := by
  induction g using ProjGenLinGroup.induction_on with
  | mk g =>
    have hi := sourceArchTraceIntegrable_affine (sourceArchScatteringKernel s)
      (sourceArchGramShift g) (sourceArchHeight_pos g) (sourceArchScatteringKernel_integrable hs)
    simp_rw [sourceArchSphericalSection_translated]
    simpa only [sourceArchAffineCoordinate] using hi.const_mul
      ((sourceArchHeight g : ℂ) ^ (-(2 * s + 1)))

theorem sourceArchSphericalIntertwiner_mk {s : ℂ} (hs : 0 < s.re) (g : GL (Fin 2) ℂ) :
    sourceArchSphericalIntertwiner s (ProjGenLinGroup.mk g) =
      ((Real.pi : ℂ) / s) * sourceArchSphericalSection (-s) (ProjGenLinGroup.mk g) := by
  have hH := sourceArchHeight_pos g
  have hH0 : (sourceArchHeight g : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
  have hk : (∫ x : ℂ, sourceArchScatteringKernel s x ∂sourceComplexTraceMeasure) =
      (Real.pi : ℂ) / s := by
    have h := sourceArchScattering_eq hs
    simpa only [sourceArchScattering, sourceArchSphericalSection_scatteringKernel] using h
  have hp : (sourceArchHeight g : ℂ) ^ (-(2 * s + 1)) *
      ((sourceArchHeight g ^ 2 : ℝ) : ℂ) = (sourceArchHeight g : ℂ) ^ (2 * (-s) + 1) := by
    rw [Complex.ofReal_pow, ← Complex.cpow_two, ← Complex.cpow_add _ _ hH0]
    congr 1
    ring
  unfold sourceArchSphericalIntertwiner
  simp_rw [sourceArchSphericalSection_translated]
  rw [integral_const_mul]
  change (sourceArchHeight g : ℂ) ^ (-(2 * s + 1)) *
    (∫ x : ℂ, sourceArchScatteringKernel s ((x + sourceArchGramShift g) /
      (sourceArchHeight g : ℂ)) ∂sourceComplexTraceMeasure) = _
  rw [sourceArchTraceIntegral_affine _ _ hH, hk, sourceArchSphericalSection_mk, sourceArchSphericalGL]
  calc
    _ = ((Real.pi : ℂ) / s) * ((sourceArchHeight g : ℂ) ^ (-(2 * s + 1)) *
        ((sourceArchHeight g ^ 2 : ℝ) : ℂ)) := by ring
    _ = _ := by rw [hp]

theorem sourceArchSphericalIntertwiner_eq {s : ℂ} (hs : 0 < s.re) (g : PGL(2, ℂ)) :
    sourceArchSphericalIntertwiner s g = ((Real.pi : ℂ) / s) * sourceArchSphericalSection (-s) g := by
  induction g using ProjGenLinGroup.induction_on with
  | mk g => exact sourceArchSphericalIntertwiner_mk hs g

theorem sourceArchSphericalIntertwiner_unitary {s : ℂ} (hs : 0 < s.re)
    (g : PGL(2, ℂ)) (k : Matrix.unitaryGroup (Fin 2) ℂ) :
    sourceArchSphericalIntertwiner s (g * sourceArchUnitaryPGL k) =
      sourceArchSphericalIntertwiner s g := by
  rw [sourceArchSphericalIntertwiner_eq hs, sourceArchSphericalIntertwiner_eq hs,
    sourceArchSphericalSection_unitary]

end
end ArtinMatthews.SourceArchJacquet
