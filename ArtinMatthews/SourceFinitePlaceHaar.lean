module

public import ArtinMatthews.SourceFinitePlaceSplit
public import ArtinMatthews.SourceAdelicStandardHaar
public import ArtinMatthews.SourceAdelicTraceHaar
public import ArtinMatthews.StandardLocalBall
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

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace SourcePhysical
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField AdeleRing ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K]

local instance finitePlaceHaarFiniteMeasurable : MeasurableSpace 𝔸ᶠ[K] := borel 𝔸ᶠ[K]
local instance finitePlaceHaarFiniteBorel : BorelSpace 𝔸ᶠ[K] := ⟨rfl⟩
local instance finitePlaceHaarCompletionMeasurable (P : HeightOneSpectrum (𝓞 K)) : MeasurableSpace (P.adicCompletion K) := borel _
local instance finitePlaceHaarCompletionBorel (P : HeightOneSpectrum (𝓞 K)) : BorelSpace (P.adicCompletion K) := ⟨rfl⟩

instance sourceKPFinitePlaceRemainder_locallyCompact (P : HeightOneSpectrum (𝓞 K)) :
    LocallyCompactSpace (sourceKPFinitePlaceRemainder K P) :=
  (sourceKPFinitePlaceRemainder_isClosed K P).locallyCompactSpace

instance sourceKPFinitePlaceRemainder_sigmaCompact (P : HeightOneSpectrum (𝓞 K)) :
    SigmaCompactSpace (sourceKPFinitePlaceRemainder K P) :=
  (sourceKPFinitePlaceRemainder_isClosed K P).sigmaCompactSpace

def sourceKPFinitePlaceRemainderIntegral (P : HeightOneSpectrum (𝓞 K)) :
    Set (sourceKPFinitePlaceRemainder K P) :=
  Subtype.val ⁻¹' (IntegralAdeles.Construction.finiteIntegralRing K : Set 𝔸ᶠ[K])

theorem sourceKPFinitePlaceRemainderIntegral_isOpen (P : HeightOneSpectrum (𝓞 K)) :
    IsOpen (sourceKPFinitePlaceRemainderIntegral K P) :=
  (IntegralAdeles.Construction.isOpen_finiteIntegralRing K).preimage continuous_subtype_val

def sourceKPFinitePlaceRemainderCompact (P : HeightOneSpectrum (𝓞 K)) :
    PositiveCompacts (sourceKPFinitePlaceRemainder K P) where
  carrier := sourceKPFinitePlaceRemainderIntegral K P
  isCompact' := (sourceKPFinitePlaceRemainder_isClosed K P).isClosedEmbedding_subtypeVal.isCompact_preimage
    (IntegralAdeles.Construction.isCompact_finiteIntegralRing K)
  interior_nonempty' := by
    rw [(sourceKPFinitePlaceRemainderIntegral_isOpen K P).interior_eq]
    exact ⟨0, (IntegralAdeles.Construction.finiteIntegralRing K).zero_mem⟩

def sourceKPFinitePlaceRemainderHaar (P : HeightOneSpectrum (𝓞 K)) :
    Measure (sourceKPFinitePlaceRemainder K P) :=
  Measure.addHaarMeasure (sourceKPFinitePlaceRemainderCompact K P)

instance sourceKPFinitePlaceRemainderHaar_isAddHaarMeasure (P : HeightOneSpectrum (𝓞 K)) :
    (sourceKPFinitePlaceRemainderHaar K P).IsAddHaarMeasure := by
  unfold sourceKPFinitePlaceRemainderHaar
  infer_instance

instance sourceKPFinitePlaceRemainderHaar_sigmaFinite (P : HeightOneSpectrum (𝓞 K)) :
    SigmaFinite (sourceKPFinitePlaceRemainderHaar K P) := by
  unfold sourceKPFinitePlaceRemainderHaar
  infer_instance

theorem sourceKPFinitePlaceRemainderHaar_integral (P : HeightOneSpectrum (𝓞 K)) :
    sourceKPFinitePlaceRemainderHaar K P (sourceKPFinitePlaceRemainderIntegral K P) = 1 :=
  Measure.addHaarMeasure_self

theorem sourceKPFiniteAdditiveSingle_mem_integral (P : HeightOneSpectrum (𝓞 K))
    (x : P.adicCompletion K) :
    sourceKPFiniteAdditiveSingle K P x ∈ IntegralAdeles.Construction.finiteIntegralRing K ↔
      x ∈ P.adicCompletionIntegers K := by
  constructor
  · intro hx
    have h := hx P
    simpa only [sourceKPFiniteAdditiveSingle_same] using h
  · intro hx Q
    by_cases hQ : Q = P
    · subst Q
      simpa only [sourceKPFiniteAdditiveSingle_same] using hx
    · rw [sourceKPFiniteAdditiveSingle_other K P x Q hQ]
      exact zero_mem _

theorem sourceKPFinitePlaceSplit_integral_preimage (P : HeightOneSpectrum (𝓞 K)) :
    (sourceKPFinitePlaceSplit K P).symm ⁻¹'
        (IntegralAdeles.Construction.finiteIntegralRing K : Set 𝔸ᶠ[K]) =
      (sourceJacquetIntegers K P : Set (P.adicCompletion K)) ×ˢ
        sourceKPFinitePlaceRemainderIntegral K P := by
  have hO : (P.adicCompletionIntegers K : Set (P.adicCompletion K)) =
      (sourceJacquetIntegers K P : Set (P.adicCompletion K)) := by
    rw [← sourceLocalBall_zero K P, sourceLocalBall_zero_eq_integerOpen]
  ext p
  change (sourceKPFiniteAdditiveSingle K P p.1 + p.2.val ∈
      IntegralAdeles.Construction.finiteIntegralRing K) ↔
    p.1 ∈ sourceJacquetIntegers K P ∧
      p.2.val ∈ IntegralAdeles.Construction.finiteIntegralRing K
  constructor
  · intro hp
    have hzero : p.2.val P = 0 := p.2.property
    have ha : p.1 ∈ P.adicCompletionIntegers K := by
      have h := hp P
      change sourceKPFiniteAdditiveSingle K P p.1 P + p.2.val P ∈
        P.adicCompletionIntegers K at h
      rwa [sourceKPFiniteAdditiveSingle_same, hzero, add_zero] at h
    refine ⟨?_, ?_⟩
    · change p.1 ∈ (sourceJacquetIntegers K P : Set (P.adicCompletion K))
      rw [← hO]
      exact ha
    have h := (IntegralAdeles.Construction.finiteIntegralRing K).sub_mem hp
      ((sourceKPFiniteAdditiveSingle_mem_integral K P p.1).mpr ha)
    simpa only [add_sub_cancel_left] using h
  · rintro ⟨ha, hb⟩
    have ha' : p.1 ∈ P.adicCompletionIntegers K := by
      change p.1 ∈ (P.adicCompletionIntegers K : Set (P.adicCompletion K))
      rw [hO]
      exact ha
    exact (IntegralAdeles.Construction.finiteIntegralRing K).add_mem
      ((sourceKPFiniteAdditiveSingle_mem_integral K P p.1).mpr ha') hb

def sourceKPFinitePlaceProductHaar (P : HeightOneSpectrum (𝓞 K)) : Measure 𝔸ᶠ[K] :=
  Measure.map (sourceKPFinitePlaceSplit K P).symm
    ((sourceJacquetHaar K P).prod (sourceKPFinitePlaceRemainderHaar K P))

instance sourceKPFinitePlaceProductHaar_isAddHaarMeasure (P : HeightOneSpectrum (𝓞 K)) :
    (sourceKPFinitePlaceProductHaar K P).IsAddHaarMeasure := by
  let : (sourceJacquetHaar K P).IsAddHaarMeasure := sourceJacquetHaar_isAddHaar K P
  exact AddEquiv.isAddHaarMeasure_map _ (sourceKPFinitePlaceSplit K P).symm.toAddEquiv
    (sourceKPFinitePlaceSplit K P).symm.continuous
    (sourceKPFinitePlaceSplit K P).continuous

theorem sourceKPFinitePlaceProductHaar_integral (P : HeightOneSpectrum (𝓞 K)) :
    sourceKPFinitePlaceProductHaar K P
      (IntegralAdeles.Construction.finiteIntegralRing K) = 1 := by
  have hm : Measurable ((sourceKPFinitePlaceSplit K P).symm :
      P.adicCompletion K × sourceKPFinitePlaceRemainder K P → 𝔸ᶠ[K]) :=
    (sourceKPFinitePlaceSplit K P).symm.continuous.measurable
  rw [sourceKPFinitePlaceProductHaar, Measure.map_apply hm
    (IntegralAdeles.Construction.isOpen_finiteIntegralRing K).measurableSet,
    sourceKPFinitePlaceSplit_integral_preimage, Measure.prod_prod,
    sourceJacquetHaar_integers, sourceKPFinitePlaceRemainderHaar_integral, one_mul]

theorem sourceKPFinitePlaceProductHaar_eq_integralHaar (P : HeightOneSpectrum (𝓞 K)) :
    sourceKPFinitePlaceProductHaar K P = sourceKPFiniteIntegralHaar K := by
  let c := Measure.addHaarScalarFactor
    (sourceKPFinitePlaceProductHaar K P) (sourceKPFiniteIntegralHaar K)
  have he : sourceKPFinitePlaceProductHaar K P = c • sourceKPFiniteIntegralHaar K :=
    Measure.isAddLeftInvariant_eq_smul _ _
  have hc : c = 1 := by
    have h := congrArg (fun μ : Measure 𝔸ᶠ[K] =>
      μ (IntegralAdeles.Construction.finiteIntegralRing K)) he
    have hc' : (c : ℝ≥0∞) = 1 := by
      simpa only [sourceKPFinitePlaceProductHaar_integral, Measure.coe_nnreal_smul_apply,
        sourceKPFiniteIntegralHaar_integral, mul_one] using h.symm
    exact ENNReal.coe_eq_one.mp hc'
  rw [hc, one_smul] at he
  exact he

def sourceKPFinitePlaceRemainderStandardHaar (P : HeightOneSpectrum (𝓞 K)) :
    Measure (sourceKPFinitePlaceRemainder K P) :=
  (sourceKPDiscriminantRoot K)⁻¹ • sourceKPFinitePlaceRemainderHaar K P

instance sourceKPFinitePlaceRemainderStandardHaar_isAddHaarMeasure
    (P : HeightOneSpectrum (𝓞 K)) :
    (sourceKPFinitePlaceRemainderStandardHaar K P).IsAddHaarMeasure :=
  Measure.IsAddHaarMeasure.smul _
    (ENNReal.inv_ne_zero.mpr (sourceKPDiscriminantRoot_ne_top K))
    (ENNReal.inv_ne_top.mpr (sourceKPDiscriminantRoot_ne_zero K))

instance sourceKPFinitePlaceRemainderStandardHaar_sFinite (P : HeightOneSpectrum (𝓞 K)) :
    SFinite (sourceKPFinitePlaceRemainderStandardHaar K P) := by
  unfold sourceKPFinitePlaceRemainderStandardHaar
  infer_instance

theorem sourceKPFiniteStandardHaar_place_split (P : HeightOneSpectrum (𝓞 K)) :
    sourceKPFiniteStandardHaar K = Measure.map (sourceKPFinitePlaceSplit K P).symm
      ((sourceJacquetHaar K P).prod (sourceKPFinitePlaceRemainderStandardHaar K P)) := by
  let : (sourceJacquetHaar K P).IsAddHaarMeasure := sourceJacquetHaar_isAddHaar K P
  have hm : AEMeasurable ((sourceKPFinitePlaceSplit K P).symm :
      P.adicCompletion K × sourceKPFinitePlaceRemainder K P → 𝔸ᶠ[K])
      ((sourceJacquetHaar K P).prod (sourceKPFinitePlaceRemainderHaar K P)) :=
    (sourceKPFinitePlaceSplit K P).symm.continuous.measurable.aemeasurable
  rw [sourceKPFiniteStandardHaar, ← sourceKPFinitePlaceProductHaar_eq_integralHaar K P,
    sourceKPFinitePlaceProductHaar, sourceKPFinitePlaceRemainderStandardHaar,
    Measure.prod_smul_right, Measure.map_smul _ hm]

end
end ArtinMatthews
