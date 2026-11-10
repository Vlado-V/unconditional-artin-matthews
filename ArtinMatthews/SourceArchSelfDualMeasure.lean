module

public import ArtinMatthews.SourceArchJacquetGaussian
public import OAI.RepresentationTheory.Weil.AdelicSplitting.ComplexNormalization
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


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
