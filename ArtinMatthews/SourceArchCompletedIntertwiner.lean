module

public import ArtinMatthews.SourceArchSphericalIntertwiner
public import ArtinMatthews.SourceArchCompletedJacquet


set_option backward.privateInPublic true
@[expose] public section

/-! The spherical intertwiner on every actual complex completion,
with its prescribed self-dual measure. -/
namespace ArtinMatthews.SourceArchJacquet

open MeasureTheory NumberField NumberField.InfinitePlace Matrix Matrix.GeneralLinearGroup
open OAI.RepresentationTheory.Weil
open scoped MatrixGroups
noncomputable section

variable (F : Type) [Field F] [NumberField F]

local instance scatteringCompletionMeasurable (v : InfinitePlace F) :
    MeasurableSpace v.Completion := borel v.Completion
local instance scatteringCompletionBorel (v : InfinitePlace F) :
    BorelSpace v.Completion := ⟨rfl⟩

omit [NumberField F] in
theorem sourceArchCompletion_rootMap (v : InfinitePlace F) (hv : IsComplex v) (x : v.Completion) :
    ProjGenLinGroup.map (sourceArchCompletionEquiv F v hv).toRingHom
      (sourcePGL2Weyl * sourcePGL2Upper x) =
      sourcePGL2Weyl * sourcePGL2Upper (sourceArchCompletionEquiv F v hv x) := by
  let e := sourceArchCompletionEquiv F v hv
  have h : GeneralLinearGroup.map e.toRingHom (sourceGL2Weyl * sourceGL2Upper x) =
      sourceGL2Weyl * sourceGL2Upper (e x) := by
    apply GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [sourceGL2Weyl, sourceGL2Upper, Matrix.mul_apply, Fin.sum_univ_two]
  change ProjGenLinGroup.map e.toRingHom
    (ProjGenLinGroup.mk sourceGL2Weyl * ProjGenLinGroup.mk (sourceGL2Upper x)) = _
  rw [← map_mul, ProjGenLinGroup.map_mk, h, map_mul]

omit [NumberField F] in
theorem sourceArchCompletedSphericalSection_translated (v : InfinitePlace F) (hv : IsComplex v)
    (s : ℂ) (g : PGL(2, v.Completion)) (x : v.Completion) :
    sourceArchCompletedSphericalSection F v hv s (sourcePGL2Weyl * sourcePGL2Upper x * g) =
      sourceArchSphericalSection s (sourcePGL2Weyl *
        sourcePGL2Upper (sourceArchCompletionEquiv F v hv x) *
          ProjGenLinGroup.map (sourceArchCompletionEquiv F v hv).toRingHom g) := by
  unfold sourceArchCompletedSphericalSection
  rw [map_mul, sourceArchCompletion_rootMap]

def sourceArchCompletedIntertwiner (v : InfinitePlace F) (hv : IsComplex v)
    (s : ℂ) (g : PGL(2, v.Completion)) : ℂ :=
  ∫ x : v.Completion,
    sourceArchCompletedSphericalSection F v hv s (sourcePGL2Weyl * sourcePGL2Upper x * g)
      ∂Local.FunctionsMetaplectic.Construction.selfDualMeasure v.Completion
        (StandardAdelic.localInfiniteCharacter F v)

theorem sourceArchCompletedIntertwiner_integrable (v : InfinitePlace F) (hv : IsComplex v)
    {s : ℂ} (hs : 0 < s.re) (g : PGL(2, v.Completion)) :
    Integrable (fun x : v.Completion => sourceArchCompletedSphericalSection F v hv s
      (sourcePGL2Weyl * sourcePGL2Upper x * g))
      (Local.FunctionsMetaplectic.Construction.selfDualMeasure v.Completion
        (StandardAdelic.localInfiniteCharacter F v)) := by
  let gC := ProjGenLinGroup.map (sourceArchCompletionEquiv F v hv).toRingHom g
  let W : ℂ → ℂ := fun x => sourceArchSphericalSection s (sourcePGL2Weyl * sourcePGL2Upper x * gC)
  have hW : Integrable W VaryingKummerAnalytic.sourceComplexTraceMeasure :=
    sourceArchSphericalIntertwiner_integrable hs gC
  simp_rw [sourceArchCompletedSphericalSection_translated]
  simpa only [W, gC] using! sourceArchCompletion_integrable F v hv W hW

theorem sourceArchCompletedIntertwiner_eq (v : InfinitePlace F) (hv : IsComplex v)
    {s : ℂ} (hs : 0 < s.re) (g : PGL(2, v.Completion)) :
    sourceArchCompletedIntertwiner F v hv s g =
      ((Real.pi : ℂ) / s) * sourceArchCompletedSphericalSection F v hv (-s) g := by
  let gC := ProjGenLinGroup.map (sourceArchCompletionEquiv F v hv).toRingHom g
  let W : ℂ → ℂ := fun x => sourceArchSphericalSection s (sourcePGL2Weyl * sourcePGL2Upper x * gC)
  have h : sourceArchCompletedIntertwiner F v hv s g = sourceArchSphericalIntertwiner s gC := by
    unfold sourceArchCompletedIntertwiner sourceArchSphericalIntertwiner
    simp_rw [sourceArchCompletedSphericalSection_translated]
    simpa only [W, gC] using! sourceArchCompletion_integral F v hv W
  rw [h, sourceArchSphericalIntertwiner_eq hs]
  rfl

theorem sourceArchCompletedIntertwiner_one (v : InfinitePlace F) (hv : IsComplex v)
    {s : ℂ} (hs : 0 < s.re) :
    sourceArchCompletedIntertwiner F v hv s 1 = (Real.pi : ℂ) / s := by
  rw [sourceArchCompletedIntertwiner_eq F v hv hs]
  simp [sourceArchCompletedSphericalSection, sourceArchSphericalSection_one]

theorem sourceArchCompletedIntertwiner_oneSixth (v : InfinitePlace F) (hv : IsComplex v) :
    sourceArchCompletedIntertwiner F v hv (1 / 6) 1 = 6 * Real.pi := by
  rw [sourceArchCompletedIntertwiner_one F v hv (by norm_num)]
  ring

end
end ArtinMatthews.SourceArchJacquet
