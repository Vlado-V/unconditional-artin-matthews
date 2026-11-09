module

public import ArtinMatthews.SourceArchCompletedMeasure
public import ArtinMatthews.SourceArchSphericalJacquet


set_option backward.privateInPublic true
@[expose] public section

/-! The spherical section and its Jacquet integral on every actual
complex completion of a number field. -/
namespace ArtinMatthews.SourceArchJacquet

open MeasureTheory NumberField NumberField.InfinitePlace Matrix Matrix.GeneralLinearGroup
open ArtinMatthews.SourceReflection
open OAI.RepresentationTheory.Weil
open scoped MatrixGroups
noncomputable section

variable (F : Type) [Field F] [NumberField F]

local instance completedJacquetMeasurable (v : InfinitePlace F) : MeasurableSpace v.Completion :=
  borel v.Completion
local instance completedJacquetBorel (v : InfinitePlace F) : BorelSpace v.Completion := ⟨rfl⟩

def sourceArchCompletedSphericalSection (v : InfinitePlace F) (hv : IsComplex v)
    (s : ℂ) (g : PGL(2, v.Completion)) : ℂ :=
  sourceArchSphericalSection s (ProjGenLinGroup.map (sourceArchCompletionEquiv F v hv).toRingHom g)

omit [NumberField F] in
theorem sourceArchCompletedSphericalSection_bigCell (v : InfinitePlace F) (hv : IsComplex v)
    (s : ℂ) (x : v.Completion) (y : v.Completionˣ) :
    sourceArchCompletedSphericalSection F v hv s
      (sourcePGL2Weyl * sourcePGL2Upper x * sourcePGL2Diagonal y) =
      sourceArchSphericalSection s (sourcePGL2Weyl *
        sourcePGL2Upper (sourceArchCompletionEquiv F v hv x) *
          sourcePGL2Diagonal (Units.map (sourceArchCompletionEquiv F v hv).toMonoidHom y)) := by
  let e := sourceArchCompletionEquiv F v hv
  have h : GeneralLinearGroup.map e.toRingHom
      (sourceGL2Weyl * sourceGL2Upper x * sourceGL2Diagonal y) =
      sourceGL2Weyl * sourceGL2Upper (e x) * sourceGL2Diagonal (Units.map e.toMonoidHom y) := by
    apply GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [sourceGL2Weyl, sourceGL2Upper, sourceGL2Diagonal,
        Matrix.mul_apply, Fin.sum_univ_two]
  unfold sourceArchCompletedSphericalSection
  rw [← map_mul, ← map_mul, ProjGenLinGroup.map_mk, h, map_mul, map_mul]

def sourceArchCompletedWhittaker (v : InfinitePlace F) (hv : IsComplex v)
    (y : v.Completionˣ) : ℂ :=
  ∫ x : v.Completion, sourceArchCompletedSphericalSection F v hv (1 / 6)
    (sourcePGL2Weyl * sourcePGL2Upper x * sourcePGL2Diagonal y) *
      StandardAdelic.localInfiniteCharacter F v (-x)
        ∂Local.FunctionsMetaplectic.Construction.selfDualMeasure v.Completion
          (StandardAdelic.localInfiniteCharacter F v)

theorem sourceArchCompletedWhittaker_integrable (v : InfinitePlace F) (hv : IsComplex v)
    (y : v.Completionˣ) :
    Integrable (fun x : v.Completion => sourceArchCompletedSphericalSection F v hv (1 / 6)
      (sourcePGL2Weyl * sourcePGL2Upper x * sourcePGL2Diagonal y) *
        StandardAdelic.localInfiniteCharacter F v (-x))
      (Local.FunctionsMetaplectic.Construction.selfDualMeasure v.Completion
        (StandardAdelic.localInfiniteCharacter F v)) := by
  simp_rw [sourceArchCompletedSphericalSection_bigCell, sourceArchCompletion_character F v hv,
    map_neg, ← sourceArchJacquetPhase_eq]
  let yC : ℂˣ := Units.map (sourceArchCompletionEquiv F v hv).toMonoidHom y
  let W : ℂ → ℂ := fun z => sourceArchSphericalSection (1 / 6)
    (sourcePGL2Weyl * sourcePGL2Upper z * sourcePGL2Diagonal yC) * sourceArchJacquetPhase z
  have hW : Integrable W VaryingKummerAnalytic.sourceComplexTraceMeasure :=
    sourceArchSphericalWhittaker_integrable yC
  simpa only [W, yC] using! sourceArchCompletion_integrable F v hv W hW

theorem sourceArchCompletedWhittaker_eq (v : InfinitePlace F) (hv : IsComplex v)
    (y : v.Completionˣ) :
    sourceArchCompletedWhittaker F v hv y =
      sourceArchSphericalWhittaker (Units.map (sourceArchCompletionEquiv F v hv).toMonoidHom y) := by
  unfold sourceArchCompletedWhittaker sourceArchSphericalWhittaker
  simp_rw [sourceArchCompletedSphericalSection_bigCell, sourceArchCompletion_character F v hv,
    map_neg, ← sourceArchJacquetPhase_eq]
  let yC : ℂˣ := Units.map (sourceArchCompletionEquiv F v hv).toMonoidHom y
  let W : ℂ → ℂ := fun z => sourceArchSphericalSection (1 / 6)
    (sourcePGL2Weyl * sourcePGL2Upper z * sourcePGL2Diagonal yC) * sourceArchJacquetPhase z
  simpa only [W, yC] using! sourceArchCompletion_integral F v hv W

theorem sourceArchCompletedWhittaker_bessel (v : InfinitePlace F) (hv : IsComplex v)
    (y : v.Completionˣ) :
    sourceArchCompletedWhittaker F v hv y =
      (sourceArchJacquetConstant * ‖(y : v.Completion)‖ : ℝ) *
        OAI.CubicEisenstein.schlafliBesselK (1 / 3 : ℂ) (4 * Real.pi * ‖(y : v.Completion)‖) := by
  rw [sourceArchCompletedWhittaker_eq, sourceArchSphericalWhittaker_eq_bessel]
  have hn : ‖((Units.map (sourceArchCompletionEquiv F v hv).toMonoidHom y : ℂˣ) : ℂ)‖ =
      ‖(y : v.Completion)‖ :=
    (Completion.isometryEquivComplexOfIsComplex hv).isometry.norm_map_of_map_zero
      (map_zero (sourceArchCompletionEquiv F v hv)) _
  rw [hn]

theorem sourceArchCompletedWhittaker_sourceProfile (v : InfinitePlace F) (hv : IsComplex v)
    (y : v.Completionˣ) :
    sourceThetaBesselProfile (4 * Real.pi) (‖(y : v.Completion)‖ ^ 2) =
      (Real.sqrt (‖(y : v.Completion)‖ ^ 2) : ℂ) * sourceArchCompletedWhittaker F v hv y /
        (sourceArchJacquetConstant : ℂ) := by
  rw [sourceArchCompletedWhittaker_eq]
  have hn : ‖((Units.map (sourceArchCompletionEquiv F v hv).toMonoidHom y : ℂˣ) : ℂ)‖ =
      ‖(y : v.Completion)‖ :=
    (Completion.isometryEquivComplexOfIsComplex hv).isometry.norm_map_of_map_zero
      (map_zero (sourceArchCompletionEquiv F v hv)) _
  simpa only [hn] using sourceThetaBesselProfile_eq_weightedWhittaker
    (Units.map (sourceArchCompletionEquiv F v hv).toMonoidHom y)

end
end ArtinMatthews.SourceArchJacquet
