module

public import ArtinMatthews.SourceComplexTensorRapid
public import ArtinMatthews.SourceComplexIdealBasis
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory Module NumberField NumberField.InfinitePlace
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField nonZeroDivisors Classical BigOperators SchwartzMap
noncomputable section
variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
local notation "CPlaces" => {v : InfinitePlace K // IsComplex v}

theorem sourceEuclideanComplexEquiv_idealEmbedding (z : I.1) :
    sourceEuclideanComplexEquiv K (mixedIdealEmbedding K I z) =
      sourceComplexFieldEmbedding K (z : K) :=
  sourceEuclideanComplexEquiv_fieldEmbedding K (z : K)

theorem sourceComplexIdealTensor_summable_norm (f : CPlaces → 𝓢(ℂ, ℂ)) (a : CPlaces → ℂ) :
    Summable (fun z : I.1 => ‖sourceComplexTensor f (a + sourceComplexFieldEmbedding K (z : K))‖) := by
  let e := sourceEuclideanComplexEquiv K
  have hs := RapidFunctions.LocalAnalysis.rapid_lattice_summable_norm (mixedIdealLattice K I)
    ((sourceComplexTensorRapid f).compLinearEquiv e) (e.symm a)
  have h := hs.comp_injective (mixedIdealToLattice K I).injective
  change Summable (fun z : I.1 =>
    ‖sourceComplexTensorRapid f (e (e.symm a + mixedIdealEmbedding K I z))‖) at h
  simpa only [map_add, ContinuousLinearEquiv.apply_symm_apply, e,
    sourceEuclideanComplexEquiv_idealEmbedding, sourceComplexTensorRapid_apply] using h

theorem sourceComplexDualIdealFourier_summable_norm (f : CPlaces → 𝓢(ℂ, ℂ))
    (a : CPlaces → ℂ) :
    Summable (fun z : (mixedTraceDualIdeal K I).1 =>
      ‖sourceComplexProductFourier (sourceComplexTensor f) (sourceComplexFieldEmbedding K (z : K)) *
        RealCharacters.LocalAnalysis.realCharacter 1
          (sourceComplexTraceForm (sourceComplexFieldEmbedding K (z : K)) a)‖) := by
  let e := sourceEuclideanComplexEquiv K
  let J := mixedTraceDualIdeal K I
  have hs := RapidFunctions.LocalAnalysis.rapid_lattice_summable_norm (mixedIdealLattice K J)
    ((sourceComplexTensorFourierRapid f).compLinearEquiv e) 0
  have h := hs.comp_injective (mixedIdealToLattice K J).injective
  change Summable (fun z : J.1 =>
    ‖sourceComplexTensorFourierRapid f (e (0 + mixedIdealEmbedding K J z))‖) at h
  simpa only [zero_add, e, sourceEuclideanComplexEquiv_idealEmbedding,
    sourceComplexTensorFourierRapid_apply, norm_mul, sourceRealCharacter_norm, mul_one] using h

end
end ArtinMatthews.VaryingKummerAnalytic
