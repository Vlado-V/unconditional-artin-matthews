module

public import ArtinMatthews.SourceArchJacquetGaussian
public import OAI.RepresentationTheory.Weil.AdelicSplitting.ScalarPlancherel


set_option backward.privateInPublic true
@[expose] public section

/-! The prescribed self-dual measure for the actual complex trace
character is twice planar volume. -/
namespace ArtinMatthews.SourceArchJacquet

open MeasureTheory
open ArtinMatthews.VaryingKummerAnalytic
open OAI.RepresentationTheory.Weil
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped Pointwise
noncomputable section

def sourceArchTraceCharacter : AddChar ℂ ℂ :=
  ComplexNormalization.LocalAnalysis.complexCharacter 2

theorem sourceArchTraceCharacter_apply (z : ℂ) :
    sourceArchTraceCharacter z = (Real.fourierChar (2 * z.re) : ℂ) := by
  change (Real.fourierChar (1 * ((2 : ℂ) * z).re) : ℂ) = _
  congr 1
  simp
  rfl

theorem sourceArchJacquetPhase_eq (z : ℂ) :
    sourceArchJacquetPhase z = sourceArchTraceCharacter (-z) := by
  rw [sourceArchTraceCharacter_apply]
  unfold sourceArchJacquetPhase
  simp

theorem sourceArchTraceHaarModulus_two :
    DeterminantMeasure.LocalAnalysis.haarModulus ℂ 2 = 4 := by
  let u : ℂˣ := Units.mk0 2 (by norm_num)
  change DeterminantMeasure.LocalAnalysis.haarModulus ℂ (u : ℂ) = 4
  rw [DeterminantMeasure.LocalAnalysis.haarModulus_unit]
  apply distribHaarChar_eq_of_measure_smul_eq_mul (μ := (volume : Measure ℂ))
    (s := Metric.ball 0 1) (r := 4)
    (Metric.measure_ball_pos volume 0 (by norm_num)).ne' measure_ball_lt_top.ne
  have he : u • Metric.ball (0 : ℂ) 1 = (2 : ℝ) • Metric.ball (0 : ℂ) 1 := by
    change (fun z : ℂ => (2 : ℂ) * z) '' Metric.ball 0 1 =
      (fun z : ℂ => (2 : ℝ) • z) '' Metric.ball 0 1
    rfl
  rw [he, Measure.addHaar_smul_of_nonneg volume (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num [Complex.finrank_real_complex]

theorem sourceArchTraceCharacter_selfDualMeasure :
    Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ sourceArchTraceCharacter =
      sourceComplexTraceMeasure := by
  rw [sourceArchTraceCharacter, ComplexNormalization.LocalAnalysis.selfDualMeasure_complex
    2 (by norm_num), sourceArchTraceHaarModulus_two]
  norm_num [sourceComplexTraceMeasure]

end
end ArtinMatthews.SourceArchJacquet
