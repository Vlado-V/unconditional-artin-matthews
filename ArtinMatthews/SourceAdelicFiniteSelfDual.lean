module

public import ArtinMatthews.SourceAdelicDifferentNorm
public import ArtinMatthews.SourceAdelicIntegralHaarProduct


set_option backward.privateInPublic true
@[expose] public section

/-! The finite standard Haar measure realizes the restricted product of the
prescribed local self-dual measures on the compact open integral adeles. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory SourcePhysical
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField AdeleRing Topology Classical ENNReal
noncomputable section
variable (K : Type) [Field K] [NumberField K]

local instance sourceKPFiniteSelfDualMeasurable : MeasurableSpace 𝔸ᶠ[K] := borel 𝔸ᶠ[K]
local instance sourceKPFiniteSelfDualBorel : BorelSpace 𝔸ᶠ[K] := ⟨rfl⟩
local instance sourceKPFiniteSelfDualCompletionMeasurable (P : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (P.adicCompletion K) := borel _
local instance sourceKPFiniteSelfDualCompletionBorel (P : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (P.adicCompletion K) := ⟨rfl⟩

theorem sourceKPLocalSelfDual_integer_ne_zero (P : HeightOneSpectrum (𝓞 K)) :
    sourceLocalSelfDual K P (P.adicCompletionIntegers K) ≠ 0 := by
  intro h
  have hp := sourceLocalBall_volume_pos K P 0
  rw [sourceLocalBall_zero, Measure.real, h, ENNReal.toReal_zero] at hp
  exact (lt_irrefl 0) hp

theorem sourceKPLocalSelfDual_integer_ne_top (P : HeightOneSpectrum (𝓞 K)) :
    sourceLocalSelfDual K P (P.adicCompletionIntegers K) ≠ ∞ := by
  let : (sourceLocalSelfDual K P).IsAddHaarMeasure := sourceLocalSelfDual_isHaar K P
  rw [← sourceLocalBall_zero K P]
  exact (sourceLocalBall_isCompact K P 0).measure_ne_top

def sourceKPNormalizedLocalSelfDual (P : HeightOneSpectrum (𝓞 K)) :
    Measure (P.adicCompletionIntegers K) :=
  (sourceLocalSelfDual K P (P.adicCompletionIntegers K))⁻¹ •
    (sourceLocalSelfDual K P).comap Subtype.val

theorem sourceKPLocalSelfDual_comap_univ (P : HeightOneSpectrum (𝓞 K)) :
    (sourceLocalSelfDual K P).comap
      (Subtype.val : P.adicCompletionIntegers K → P.adicCompletion K) Set.univ =
        sourceLocalSelfDual K P (P.adicCompletionIntegers K) := by
  let f : P.adicCompletionIntegers K → P.adicCompletion K := Subtype.val
  have hf : Topology.IsOpenEmbedding f :=
    (Valued.isOpen_valuationSubring (P.adicCompletion K)).isOpenEmbedding_subtypeVal
  have hr : Set.range f = (P.adicCompletionIntegers K : Set (P.adicCompletion K)) := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      exact x.property
    · intro ha
      exact ⟨⟨a, ha⟩, rfl⟩
  simpa only [Set.image_univ, hr] using
    hf.measurableEmbedding.comap_apply (sourceLocalSelfDual K P) Set.univ

instance sourceKPNormalizedLocalSelfDual_isAddHaarMeasure (P : HeightOneSpectrum (𝓞 K)) :
    (sourceKPNormalizedLocalSelfDual K P).IsAddHaarMeasure := by
  let : (sourceLocalSelfDual K P).IsAddHaarMeasure := sourceLocalSelfDual_isHaar K P
  have : ((sourceLocalSelfDual K P).comap
      (Subtype.val : P.adicCompletionIntegers K → P.adicCompletion K)).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.comap (sourceLocalSelfDual K P) (mH := inferInstance)
      (f := (P.adicCompletionIntegers K).subtype.toAddMonoidHom)
      (Valued.isOpen_valuationSubring (P.adicCompletion K)).isOpenEmbedding_subtypeVal
  exact Measure.IsAddHaarMeasure.smul _
    (ENNReal.inv_ne_zero.mpr (sourceKPLocalSelfDual_integer_ne_top K P))
    (ENNReal.inv_ne_top.mpr (sourceKPLocalSelfDual_integer_ne_zero K P))

instance sourceKPNormalizedLocalSelfDual_isProbabilityMeasure (P : HeightOneSpectrum (𝓞 K)) :
    IsProbabilityMeasure (sourceKPNormalizedLocalSelfDual K P) := by
  constructor
  rw [sourceKPNormalizedLocalSelfDual, Measure.smul_apply]
  change (sourceLocalSelfDual K P (P.adicCompletionIntegers K))⁻¹ *
    ((sourceLocalSelfDual K P).comap
      (Subtype.val : P.adicCompletionIntegers K → P.adicCompletion K)) Set.univ = 1
  rw [sourceKPLocalSelfDual_comap_univ]
  exact ENNReal.inv_mul_cancel (sourceKPLocalSelfDual_integer_ne_zero K P)
    (sourceKPLocalSelfDual_integer_ne_top K P)

theorem sourceKPNormalizedLocalSelfDual_eq (P : HeightOneSpectrum (𝓞 K)) :
    sourceKPNormalizedLocalSelfDual K P = sourceKPIntegralPlaceHaar K P :=
  Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

def sourceKPFiniteSelfDualIntegralProduct :
    Measure (IntegralAdeles.Construction.finiteIntegralRing K) :=
  (∏ᶠ P : HeightOneSpectrum (𝓞 K), sourceLocalSelfDual K P (P.adicCompletionIntegers K)) •
    Measure.map (sourceKPFiniteIntegralProductAddEquiv K)
      (Measure.infinitePi (sourceKPNormalizedLocalSelfDual K))

theorem sourceKPFiniteStandardHaarRestriction_eq_selfDualProduct :
    (sourceKPFiniteStandardHaar K).comap
      (Subtype.val : IntegralAdeles.Construction.finiteIntegralRing K → 𝔸ᶠ[K]) =
        sourceKPFiniteSelfDualIntegralProduct K := by
  rw [sourceKPFiniteSelfDualIntegralProduct, sourceKPLocalSelfDual_integer_product,
    show sourceKPNormalizedLocalSelfDual K = sourceKPIntegralPlaceHaar K from
      funext (sourceKPNormalizedLocalSelfDual_eq K)]
  exact sourceKPFiniteStandardHaarRestriction_eq_product K

theorem sourceKPFiniteStandardHaar_restrict_integral :
    (sourceKPFiniteStandardHaar K).restrict
      (IntegralAdeles.Construction.finiteIntegralRing K) =
        (sourceKPFiniteSelfDualIntegralProduct K).map
          (Subtype.val : IntegralAdeles.Construction.finiteIntegralRing K → 𝔸ᶠ[K]) := by
  rw [← sourceKPFiniteStandardHaarRestriction_eq_selfDualProduct]
  let f : IntegralAdeles.Construction.finiteIntegralRing K → 𝔸ᶠ[K] := Subtype.val
  have hf : Topology.IsOpenEmbedding f :=
    (IntegralAdeles.Construction.isOpen_finiteIntegralRing K).isOpenEmbedding_subtypeVal
  have hr : Set.range f = (IntegralAdeles.Construction.finiteIntegralRing K : Set 𝔸ᶠ[K]) := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      exact x.property
    · intro ha
      exact ⟨⟨a, ha⟩, rfl⟩
  simpa only [hr] using
    (hf.measurableEmbedding.map_comap (sourceKPFiniteStandardHaar K)).symm

end
end ArtinMatthews
