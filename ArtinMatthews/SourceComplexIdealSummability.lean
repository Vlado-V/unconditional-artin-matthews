module

public import ArtinMatthews.SourceComplexTensorRapid


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
