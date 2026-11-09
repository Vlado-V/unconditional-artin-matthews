module

public import ArtinMatthews.SourceAdelicFiniteSelfDual
public import ArtinMatthews.SourceAdelicArchSelfDual
public import ArtinMatthews.SLocalSourceComplements


set_option backward.privateInPublic true
@[expose] public section

/-! The discriminant-normalized global Haar measure is assembled from the
prescribed local trace-self-dual factors. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField AdeleRing Topology Classical ENNReal
noncomputable section
variable (K : Type) [Field K] [NumberField K]

local instance sourceKPTraceHaarFiniteMeasurable : MeasurableSpace 𝔸ᶠ[K] := borel 𝔸ᶠ[K]
local instance sourceKPTraceHaarFiniteBorel : BorelSpace 𝔸ᶠ[K] := ⟨rfl⟩
local instance sourceKPTraceHaarAdelicMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance sourceKPTraceHaarAdelicBorel : BorelSpace 𝔸[K] := ⟨rfl⟩
local instance sourceKPTraceHaarCompletionMeasurable (v : InfinitePlace K) :
    MeasurableSpace v.Completion := borel _
local instance sourceKPTraceHaarInfiniteMeasurable : MeasurableSpace (InfiniteAdeleRing K) :=
  inferInstanceAs (MeasurableSpace (∀ v : InfinitePlace K, v.Completion))

instance sourceKPFiniteAdeleSecondCountable : SecondCountableTopology 𝔸ᶠ[K] := by
  have : SecondCountableTopology ↥(IntegralAdeles.Construction.finiteIntegralRing K : Set 𝔸ᶠ[K]) :=
    sourceKPFiniteIntegralSecondCountable K
  let U : K → Set 𝔸ᶠ[K] := fun q =>
    (Homeomorph.addRight (algebraMap K 𝔸ᶠ[K] q)) ''
      (IntegralAdeles.Construction.finiteIntegralRing K : Set 𝔸ᶠ[K])
  let (q : K) : SecondCountableTopology (U q) :=
    ((Homeomorph.addRight (algebraMap K 𝔸ᶠ[K] q)).image
      (IntegralAdeles.Construction.finiteIntegralRing K : Set 𝔸ᶠ[K])).symm.secondCountableTopology
  apply TopologicalSpace.secondCountableTopology_of_countable_cover (U := U)
  · intro q
    exact (Homeomorph.addRight _).isOpenMap _
      (IntegralAdeles.Construction.isOpen_finiteIntegralRing K)
  · apply Set.eq_univ_of_forall
    intro a
    obtain ⟨q, hq⟩ := CompactQuotient.Construction.exists_rational_finite_integral_remainder K a
    exact Set.mem_iUnion.mpr ⟨q, a - algebraMap K 𝔸ᶠ[K] q, hq, sub_add_cancel _ _⟩

theorem sourceKPFiniteHaar_unique_selfDual_extension (μ : Measure 𝔸ᶠ[K])
    [μ.IsAddHaarMeasure]
    (hμ : μ.comap (Subtype.val : IntegralAdeles.Construction.finiteIntegralRing K → 𝔸ᶠ[K]) =
      sourceKPFiniteSelfDualIntegralProduct K) : μ = sourceKPFiniteStandardHaar K := by
  let ν := sourceKPFiniteStandardHaar K
  let c := Measure.addHaarScalarFactor μ ν
  have he : μ = c • ν := Measure.isAddLeftInvariant_eq_smul μ ν
  have hm : μ (IntegralAdeles.Construction.finiteIntegralRing K) =
      (sourceKPDiscriminantRoot K)⁻¹ := by
    have h := congrArg (fun m : Measure (IntegralAdeles.Construction.finiteIntegralRing K) => m Set.univ)
      (hμ.trans (sourceKPFiniteStandardHaarRestriction_eq_selfDualProduct K).symm)
    simpa only [sourceKPFiniteIntegral_comap_univ, sourceKPFiniteStandardHaar_integral] using h
  have hscale : (sourceKPDiscriminantRoot K)⁻¹ =
      (c : ℝ≥0∞) * (sourceKPDiscriminantRoot K)⁻¹ := by
    have h := congrArg (fun m : Measure 𝔸ᶠ[K] =>
      m (IntegralAdeles.Construction.finiteIntegralRing K)) he
    simpa only [hm, Measure.coe_nnreal_smul_apply, ν, sourceKPFiniteStandardHaar_integral] using h
  have hr : 0 < ((sourceKPDiscriminantRoot K)⁻¹).toReal :=
    ENNReal.toReal_pos (ENNReal.inv_ne_zero.mpr (sourceKPDiscriminantRoot_ne_top K))
      (ENNReal.inv_ne_top.mpr (sourceKPDiscriminantRoot_ne_zero K))
  have hc : (c : ℝ) = 1 := by
    have h := congrArg ENNReal.toReal hscale
    simp only [ENNReal.toReal_mul, ENNReal.coe_toReal] at h
    apply mul_right_cancel₀ hr.ne'
    simpa only [one_mul] using h.symm
  have hc' : c = 1 := NNReal.coe_injective hc
  simpa only [hc', one_smul] using he

def sourceKPAdelicTraceProduct : Measure 𝔸[K] :=
  Measure.map (sourceKPAdelicMixedAddEquiv K).symm
    (((sourceKPArchSelfDualProduct K).map (InfiniteAdeleRing.ringEquiv_mixedSpace K)).prod
      (sourceKPFiniteStandardHaar K))

theorem sourceKPAdelicTraceProduct_eq_standard
    (hc : ∀ v : InfinitePlace K, InfinitePlace.IsComplex v) :
    sourceKPAdelicTraceProduct K = sourceKPAdelicStandardHaar K := by
  rw [sourceKPAdelicTraceProduct, sourceKPArchSelfDualProduct_mixedSpace K hc]
  rfl

theorem sourceKPAdelicTraceProduct_isAddHaarMeasure
    (hc : ∀ v : InfinitePlace K, InfinitePlace.IsComplex v) :
    (sourceKPAdelicTraceProduct K).IsAddHaarMeasure := by
  rw [sourceKPAdelicTraceProduct_eq_standard K hc]
  infer_instance

theorem sourceKPAdelicTraceProduct_fundamentalDomain
    (hc : ∀ v : InfinitePlace K, InfinitePlace.IsComplex v) :
    sourceKPAdelicTraceProduct K (sourceKPAdelicFundamentalDomain K) = 1 := by
  rw [sourceKPAdelicTraceProduct_eq_standard K hc, sourceKPAdelicStandardHaar_fundamentalDomain]

theorem sourceKPAdelicTraceProduct_eq_standard_of_primitiveRoot
    {ζ : K} (hζ : IsPrimitiveRoot ζ 12) :
    sourceKPAdelicTraceProduct K = sourceKPAdelicStandardHaar K := by
  let := source_isTotallyComplex K hζ
  exact sourceKPAdelicTraceProduct_eq_standard K (fun v => IsTotallyComplex.isComplex v)

theorem sourceKPAdelicTraceProduct_fundamentalDomain_of_primitiveRoot
    {ζ : K} (hζ : IsPrimitiveRoot ζ 12) :
    sourceKPAdelicTraceProduct K (sourceKPAdelicFundamentalDomain K) = 1 := by
  rw [sourceKPAdelicTraceProduct_eq_standard_of_primitiveRoot K hζ,
    sourceKPAdelicStandardHaar_fundamentalDomain]

end
end ArtinMatthews
