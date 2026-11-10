module

public import OAI.RepresentationTheory.Weil.AdelicSplitting.RapidFunctions
public import ArtinMatthews.SourceComplexProductTest
public import ArtinMatthews.SourceTraceFourierDecay
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
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

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap
noncomputable section

theorem sourceComplexTraceFourier_continuous (f : 𝓢(ℂ, ℂ)) :
    Continuous (sourceComplexTraceFourier f) := by
  have heq : sourceComplexTraceFourier f =
      fun z => 2 * (𝓕 f : 𝓢(ℂ, ℂ)) ((2 : ℝ) • star z) :=
    funext (source_complex_trace_fourier_schwartz_eq f)
  rw [heq]
  exact continuous_const.mul ((𝓕 f : 𝓢(ℂ, ℂ)).continuous.comp
    ((continuous_star : Continuous (fun z : ℂ => star z)).const_smul (2 : ℝ)))

def sourceComplexTraceFourierRapid (f : 𝓢(ℂ, ℂ)) :
    OAI.RepresentationTheory.Weil.AdelicSplitting.RapidFunctions.LocalAnalysis.RapidFunction ℂ where
  toContinuousMap := ⟨sourceComplexTraceFourier f, sourceComplexTraceFourier_continuous f⟩
  decay n := ⟨sourceComplexTraceDecayConstant f n, sourceComplexTraceDecayConstant_nonneg f n,
    source_complex_trace_fourier_rapid_decay f n⟩

variable {ι : Type*} [Fintype ι]

def sourceComplexProductTestRapid :
    OAI.RepresentationTheory.Weil.AdelicSplitting.RapidFunctions.LocalAnalysis.RapidFunction
      (ι → ℂ) :=
  OAI.RepresentationTheory.Weil.AdelicSplitting.RapidFunctions.LocalAnalysis.schwartzRapidFunction
    sourceComplexProductSchwartzTest

theorem sourceComplexProductTestRapid_apply (x : ι → ℂ) :
    sourceComplexProductTestRapid x = sourceComplexProductTest x := rfl

def sourceComplexProductFourierRapid :
    OAI.RepresentationTheory.Weil.AdelicSplitting.RapidFunctions.LocalAnalysis.RapidFunction
      (ι → ℂ) :=
  OAI.RepresentationTheory.Weil.AdelicSplitting.RapidFunctions.LocalAnalysis.piRapidFunction
    (fun _ : ι => sourceComplexTraceFourierRapid sourceAnnularSchwartzTest)

theorem sourceComplexProductFourierRapid_apply (x : ι → ℂ) :
    sourceComplexProductFourierRapid x = sourceComplexProductFourier sourceComplexProductTest x := by
  change (∏ i, sourceComplexTraceFourier sourceAnnularSchwartzTest (x i)) = _
  exact (sourceComplexProductTest_fourier_tensor x).symm

theorem sourceComplexProductFourier_continuous :
    Continuous (sourceComplexProductFourier (sourceComplexProductTest (ι := ι))) := by
  have h := (sourceComplexProductFourierRapid (ι := ι)).continuous
  change Continuous (fun x : ι → ℂ => sourceComplexProductFourierRapid x) at h
  simpa only [sourceComplexProductFourierRapid_apply] using h

end
end ArtinMatthews.VaryingKummerAnalytic
