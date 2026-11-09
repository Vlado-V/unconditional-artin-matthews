module

public import ArtinMatthews.SourceAdelicTraceHaar
public import Mathlib.MeasureTheory.Integral.Prod


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
