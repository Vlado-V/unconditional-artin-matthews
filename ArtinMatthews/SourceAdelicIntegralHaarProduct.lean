module

public import ArtinMatthews.SourceAdelicStandardHaar
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import OAI.RepresentationTheory.Weil.AdelicSplitting.LocalCompact


set_option backward.privateInPublic true
@[expose] public section

/-! The restriction of the actual finite Haar measure to integral adeles
is the product of the normalized local integral Haar measures. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField AdeleRing Topology Classical ENNReal
noncomputable section
variable (K : Type) [Field K] [NumberField K]

local instance sourceKPIntegralProductFiniteMeasurable : MeasurableSpace 𝔸ᶠ[K] := borel 𝔸ᶠ[K]
local instance sourceKPIntegralProductFiniteBorel : BorelSpace 𝔸ᶠ[K] := ⟨rfl⟩
local instance sourceKPIntegralProductCompletionMeasurable (P : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (P.adicCompletion K) := borel _
local instance sourceKPIntegralProductCompletionBorel (P : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (P.adicCompletion K) := ⟨rfl⟩

instance sourceKPRingOfIntegersCountable : Countable (𝓞 K) :=
  (FaithfulSMul.algebraMap_injective (𝓞 K) K).countable

instance sourceKPIdealCountable : Countable (Ideal (𝓞 K)) := by
  let f : Ideal (𝓞 K) → Finset (𝓞 K) := fun I => I.fg_of_isNoetherianRing.choose
  have hf (I : Ideal (𝓞 K)) : Ideal.span (f I : Set (𝓞 K)) = I :=
    I.fg_of_isNoetherianRing.choose_spec
  have hi : Function.Injective f := by
    intro I J h
    rw [← hf I, ← hf J, h]
  exact hi.countable

instance sourceKPFinitePrimeCountable : Countable (HeightOneSpectrum (𝓞 K)) :=
  HeightOneSpectrum.asIdeal_injective.countable

def sourceKPIntegralPlacePositiveCompact (P : HeightOneSpectrum (𝓞 K)) :
    TopologicalSpace.PositiveCompacts (P.adicCompletionIntegers K) where
  carrier := Set.univ
  isCompact' := isCompact_univ
  interior_nonempty' := by simp

def sourceKPIntegralPlaceHaar (P : HeightOneSpectrum (𝓞 K)) :
    Measure (P.adicCompletionIntegers K) :=
  Measure.addHaarMeasure (sourceKPIntegralPlacePositiveCompact K P)

instance sourceKPIntegralPlaceHaar_isAddHaarMeasure (P : HeightOneSpectrum (𝓞 K)) :
    (sourceKPIntegralPlaceHaar K P).IsAddHaarMeasure := by
  unfold sourceKPIntegralPlaceHaar
  infer_instance

instance sourceKPIntegralPlaceHaar_isProbabilityMeasure (P : HeightOneSpectrum (𝓞 K)) :
    IsProbabilityMeasure (sourceKPIntegralPlaceHaar K P) :=
  ⟨Measure.addHaarMeasure_self⟩

def sourceKPIntegralProductHaar : Measure (∀ P : HeightOneSpectrum (𝓞 K), P.adicCompletionIntegers K) :=
  Measure.infinitePi (sourceKPIntegralPlaceHaar K)

instance sourceKPIntegralProductHaar_isProbabilityMeasure :
    IsProbabilityMeasure (sourceKPIntegralProductHaar K) := by
  unfold sourceKPIntegralProductHaar
  infer_instance

instance sourceKPIntegralProductHaar_isAddLeftInvariant :
    (sourceKPIntegralProductHaar K).IsAddLeftInvariant where
  map_add_left_eq_self a := by
    change (Measure.infinitePi (sourceKPIntegralPlaceHaar K)).map
      (fun x P => a P + x P) = _
    rw [Measure.infinitePi_map_pi _ (fun _ => measurable_const_add _)]
    simp only [map_add_left_eq_self]
    rfl

instance sourceKPIntegralProductHaar_isAddHaarMeasure :
    (sourceKPIntegralProductHaar K).IsAddHaarMeasure := by
  apply Measure.isAddHaarMeasure_of_isCompact_nonempty_interior
    (sourceKPIntegralProductHaar K) Set.univ isCompact_univ
  · simp
  · simp
  · simp

def sourceKPFiniteIntegralProductAddEquiv :
    (∀ P : HeightOneSpectrum (𝓞 K), P.adicCompletionIntegers K) ≃+
      IntegralAdeles.Construction.finiteIntegralRing K where
  toFun := IntegralAdeles.Construction.finiteIntegralProductHomeomorph K
  invFun := (IntegralAdeles.Construction.finiteIntegralProductHomeomorph K).symm
  left_inv := (IntegralAdeles.Construction.finiteIntegralProductHomeomorph K).left_inv
  right_inv := (IntegralAdeles.Construction.finiteIntegralProductHomeomorph K).right_inv
  map_add' x y := by
    apply Subtype.ext
    ext P
    rfl

instance sourceKPFiniteIntegralSecondCountable :
    SecondCountableTopology (IntegralAdeles.Construction.finiteIntegralRing K) :=
  (IntegralAdeles.Construction.finiteIntegralProductHomeomorph K).symm.secondCountableTopology

def sourceKPFiniteIntegralProductHaar :
    Measure (IntegralAdeles.Construction.finiteIntegralRing K) :=
  Measure.map (sourceKPFiniteIntegralProductAddEquiv K) (sourceKPIntegralProductHaar K)

instance sourceKPFiniteIntegralProductHaar_isProbabilityMeasure :
    IsProbabilityMeasure (sourceKPFiniteIntegralProductHaar K) := by
  unfold sourceKPFiniteIntegralProductHaar
  infer_instance

instance sourceKPFiniteIntegralProductHaar_isAddHaarMeasure :
    (sourceKPFiniteIntegralProductHaar K).IsAddHaarMeasure :=
  AddEquiv.isAddHaarMeasure_map _ (sourceKPFiniteIntegralProductAddEquiv K)
    (IntegralAdeles.Construction.finiteIntegralProductHomeomorph K).continuous
    (IntegralAdeles.Construction.finiteIntegralProductHomeomorph K).symm.continuous

def sourceKPFiniteIntegralHaarRestriction :
    Measure (IntegralAdeles.Construction.finiteIntegralRing K) :=
  (sourceKPFiniteIntegralHaar K).comap Subtype.val

theorem sourceKPFiniteIntegral_comap_univ (μ : Measure 𝔸ᶠ[K]) :
    μ.comap (Subtype.val : IntegralAdeles.Construction.finiteIntegralRing K → 𝔸ᶠ[K]) Set.univ =
      μ (IntegralAdeles.Construction.finiteIntegralRing K) := by
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
  simpa only [Set.image_univ, hr] using hf.measurableEmbedding.comap_apply μ Set.univ

instance sourceKPFiniteIntegralHaarRestriction_isAddHaarMeasure :
    (sourceKPFiniteIntegralHaarRestriction K).IsAddHaarMeasure := by
  exact Measure.IsAddHaarMeasure.comap (sourceKPFiniteIntegralHaar K)
    (mH := inferInstance)
    (f := (IntegralAdeles.Construction.finiteIntegralRing K).subtype.toAddMonoidHom)
    (IntegralAdeles.Construction.isOpen_finiteIntegralRing K).isOpenEmbedding_subtypeVal

instance sourceKPFiniteIntegralHaarRestriction_isProbabilityMeasure :
    IsProbabilityMeasure (sourceKPFiniteIntegralHaarRestriction K) := by
  constructor
  change (sourceKPFiniteIntegralHaar K).comap
    (Subtype.val : IntegralAdeles.Construction.finiteIntegralRing K → 𝔸ᶠ[K]) Set.univ = 1
  rw [sourceKPFiniteIntegral_comap_univ, sourceKPFiniteIntegralHaar_integral]

theorem sourceKPFiniteIntegralHaarRestriction_eq_product :
    sourceKPFiniteIntegralHaarRestriction K = sourceKPFiniteIntegralProductHaar K := by
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

theorem sourceKPFiniteStandardHaarRestriction_eq_product :
    (sourceKPFiniteStandardHaar K).comap
      (Subtype.val : IntegralAdeles.Construction.finiteIntegralRing K → 𝔸ᶠ[K]) =
        (sourceKPDiscriminantRoot K)⁻¹ • sourceKPFiniteIntegralProductHaar K := by
  rw [sourceKPFiniteStandardHaar, Measure.comap_smul]
  change (sourceKPDiscriminantRoot K)⁻¹ • sourceKPFiniteIntegralHaarRestriction K = _
  rw [sourceKPFiniteIntegralHaarRestriction_eq_product]

end
end ArtinMatthews
