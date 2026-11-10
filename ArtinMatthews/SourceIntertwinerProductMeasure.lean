module

public import ArtinMatthews.SourceAdelicTraceHaar
public import ArtinMatthews.SLocalSourceComplements
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

namespace ArtinMatthews

open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance traceProductAdelicMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance traceProductAdelicBorel : BorelSpace 𝔸[K] := ⟨rfl⟩
local instance traceProductFiniteMeasurable : MeasurableSpace 𝔸ᶠ[K] := borel 𝔸ᶠ[K]
local instance traceProductFiniteBorel : BorelSpace 𝔸ᶠ[K] := ⟨rfl⟩
local instance traceProductCompletionMeasurable (v : InfinitePlace K) : MeasurableSpace v.Completion := borel _
local instance traceProductCompletionBorel (v : InfinitePlace K) : BorelSpace v.Completion := ⟨rfl⟩
local instance traceProductCompletionSecondCountable (v : InfinitePlace K) : SecondCountableTopology v.Completion := by
  rcases v.isReal_or_isComplex with hv | hv
  · exact (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv).toHomeomorph.secondCountableTopology
  · exact (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).toHomeomorph.secondCountableTopology
local instance traceProductInfiniteMeasurable : MeasurableSpace (InfiniteAdeleRing K) :=
  inferInstanceAs (MeasurableSpace (∀ v : InfinitePlace K, v.Completion))
local instance traceProductInfiniteBorel : BorelSpace (InfiniteAdeleRing K) := by
  change BorelSpace (∀ v : InfinitePlace K, v.Completion)
  infer_instance

include hζ in
theorem sourceKPTraceProduct_integral_separated
    (f : InfiniteAdeleRing K → ℂ) (g : 𝔸ᶠ[K] → ℂ) :
    (∫ y : 𝔸[K], f y.1 * g y.2 ∂sourceKPAdelicTraceProduct K) =
      (∫ x, f x ∂sourceKPArchSelfDualProduct K) *
        (∫ y, g y ∂sourceKPFiniteStandardHaar K) := by
  let := source_isTotallyComplex K hζ
  have hc (v : InfinitePlace K) : InfinitePlace.IsComplex v :=
    IsTotallyComplex.isComplex v
  let e := (OAI.RepresentationTheory.Weil.AdelicSplitting.CompactQuotient.Construction.adelicMixedHomeomorph K).toMeasurableEquiv
  let a := (OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph K).toMeasurableEquiv
  have ha : (a : InfiniteAdeleRing K → mixedEmbedding.mixedSpace K) =
      InfiniteAdeleRing.ringEquiv_mixedSpace K := by
    funext x
    rfl
  have hm : (sourceKPArchSelfDualProduct K).map a = sourceKPArchStandardHaar K := by
    rw [ha]
    exact sourceKPArchSelfDualProduct_mixedSpace K hc
  let : SFinite ((sourceKPArchSelfDualProduct K).map a) := by
    rw [hm]
    infer_instance
  change (∫ y : 𝔸[K], f y.1 * g y.2 ∂Measure.map e.symm
    (((sourceKPArchSelfDualProduct K).map a).prod (sourceKPFiniteStandardHaar K))) = _
  rw [integral_map_equiv]
  change (∫ p : mixedEmbedding.mixedSpace K × 𝔸ᶠ[K],
    f (a.symm p.1) * g p.2
      ∂((sourceKPArchSelfDualProduct K).map a).prod (sourceKPFiniteStandardHaar K)) = _
  calc
    _ = (∫ x, f (a.symm x) ∂(sourceKPArchSelfDualProduct K).map a) *
        (∫ y, g y ∂sourceKPFiniteStandardHaar K) :=
      integral_prod_mul (μ := (sourceKPArchSelfDualProduct K).map a)
        (ν := sourceKPFiniteStandardHaar K) (fun x => f (a.symm x)) g
    _ = _ := by
      congr 1
      refine (integral_map_equiv (μ := sourceKPArchSelfDualProduct K) a
        (fun x => f (a.symm x))).trans ?_
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => congrArg f (a.symm_apply_apply x))

end
end ArtinMatthews
