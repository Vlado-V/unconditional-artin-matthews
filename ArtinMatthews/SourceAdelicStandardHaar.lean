module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop
public import ArtinMatthews.SourceAdelicHaarUnfolding


set_option backward.privateInPublic true
@[expose] public section

/-! An explicit additive adelic Haar measure whose rational fundamental
domain has mass one.  The archimedean factor is mixed-space Lebesgue measure
scaled by `2 ^ nrComplexPlaces K`.  The finite factor is normalized on the
integral adeles and then scaled by the inverse square root of the absolute
discriminant. -/
namespace ArtinMatthews
open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField AdeleRing Topology Classical ENNReal
noncomputable section
variable (K : Type) [Field K] [NumberField K]

local instance : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance : BorelSpace 𝔸[K] := ⟨rfl⟩
local instance : MeasurableSpace 𝔸ᶠ[K] := borel 𝔸ᶠ[K]
local instance : BorelSpace 𝔸ᶠ[K] := ⟨rfl⟩

instance sourceKPFiniteAdeleSigmaCompact : SigmaCompactSpace 𝔸ᶠ[K] := by
  let C : K → Set 𝔸ᶠ[K] := fun q =>
    (fun a => a + algebraMap K 𝔸ᶠ[K] q) ''
      (IntegralAdeles.Construction.finiteIntegralRing K : Set 𝔸ᶠ[K])
  apply SigmaCompactSpace.of_countable (Set.range C) (Set.countable_range C)
  · rintro _ ⟨q, rfl⟩
    exact (IntegralAdeles.Construction.isCompact_finiteIntegralRing K).image
      (continuous_id.add continuous_const)
  · apply Set.eq_univ_of_forall
    intro a
    obtain ⟨q, hq⟩ := CompactQuotient.Construction.exists_rational_finite_integral_remainder K a
    exact ⟨C q, ⟨q, rfl⟩, a - algebraMap K 𝔸ᶠ[K] q, hq, sub_add_cancel _ _⟩

def sourceKPFiniteIntegralPositiveCompact : TopologicalSpace.PositiveCompacts 𝔸ᶠ[K] where
  carrier := IntegralAdeles.Construction.finiteIntegralRing K
  isCompact' := IntegralAdeles.Construction.isCompact_finiteIntegralRing K
  interior_nonempty' := by
    rw [(IntegralAdeles.Construction.isOpen_finiteIntegralRing K).interior_eq]
    exact ⟨0, (IntegralAdeles.Construction.finiteIntegralRing K).zero_mem⟩

def sourceKPFiniteIntegralHaar : Measure 𝔸ᶠ[K] :=
  Measure.addHaarMeasure (sourceKPFiniteIntegralPositiveCompact K)

instance sourceKPFiniteIntegralHaar_isAddHaarMeasure :
    (sourceKPFiniteIntegralHaar K).IsAddHaarMeasure := by
  unfold sourceKPFiniteIntegralHaar
  infer_instance

@[simp] theorem sourceKPFiniteIntegralHaar_integral :
    sourceKPFiniteIntegralHaar K (IntegralAdeles.Construction.finiteIntegralRing K) = 1 :=
  Measure.addHaarMeasure_self

def sourceKPDiscriminantRoot : ℝ≥0∞ := NNReal.sqrt ‖discr K‖₊

theorem sourceKPDiscriminantRoot_ne_zero : sourceKPDiscriminantRoot K ≠ 0 := by
  simp [sourceKPDiscriminantRoot, NNReal.sqrt_eq_zero, discr_ne_zero K]

theorem sourceKPDiscriminantRoot_ne_top : sourceKPDiscriminantRoot K ≠ ∞ :=
  ENNReal.coe_ne_top

def sourceKPFiniteStandardHaar : Measure 𝔸ᶠ[K] :=
  (sourceKPDiscriminantRoot K)⁻¹ • sourceKPFiniteIntegralHaar K

instance sourceKPFiniteStandardHaar_isAddHaarMeasure :
    (sourceKPFiniteStandardHaar K).IsAddHaarMeasure :=
  Measure.IsAddHaarMeasure.smul _
    (ENNReal.inv_ne_zero.mpr (sourceKPDiscriminantRoot_ne_top K))
    (ENNReal.inv_ne_top.mpr (sourceKPDiscriminantRoot_ne_zero K))

@[simp] theorem sourceKPFiniteStandardHaar_integral :
    sourceKPFiniteStandardHaar K (IntegralAdeles.Construction.finiteIntegralRing K) =
      (sourceKPDiscriminantRoot K)⁻¹ := by
  simp [sourceKPFiniteStandardHaar]

def sourceKPArchStandardHaar : Measure (mixedEmbedding.mixedSpace K) :=
  (2 : ℝ≥0∞) ^ nrComplexPlaces K • volume

instance sourceKPArchStandardHaar_isAddHaarMeasure :
    (sourceKPArchStandardHaar K).IsAddHaarMeasure :=
  Measure.IsAddHaarMeasure.smul _ (by positivity) (by simp)

theorem sourceKPArchStandardHaar_fundamentalDomain :
    sourceKPArchStandardHaar K (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis K)) =
      sourceKPDiscriminantRoot K := by
  rw [sourceKPArchStandardHaar, Measure.smul_apply,
    mixedEmbedding.volume_fundamentalDomain_latticeBasis]
  change (2 : ℝ≥0∞) ^ nrComplexPlaces K *
    ((2 : ℝ≥0∞)⁻¹ ^ nrComplexPlaces K * sourceKPDiscriminantRoot K) = _
  rw [← mul_assoc, ← mul_pow]
  rw [ENNReal.mul_inv_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num),
    one_pow, one_mul]

def sourceKPAdelicMixedAddEquiv :
    𝔸[K] ≃+ (mixedEmbedding.mixedSpace K × 𝔸ᶠ[K]) :=
  (RingEquiv.prodCongr (InfiniteAdeleRing.ringEquiv_mixedSpace K)
    (RingEquiv.refl 𝔸ᶠ[K])).toAddEquiv

theorem sourceKPAdelicMixedAddEquiv_continuous :
    Continuous (sourceKPAdelicMixedAddEquiv K) :=
  (CompactQuotient.Construction.adelicMixedHomeomorph K).continuous

theorem sourceKPAdelicMixedAddEquiv_symm_continuous :
    Continuous (sourceKPAdelicMixedAddEquiv K).symm :=
  (CompactQuotient.Construction.adelicMixedHomeomorph K).symm.continuous

def sourceKPAdelicStandardHaar : Measure 𝔸[K] :=
  Measure.map (sourceKPAdelicMixedAddEquiv K).symm
    ((sourceKPArchStandardHaar K).prod (sourceKPFiniteStandardHaar K))

instance sourceKPAdelicStandardHaar_isAddHaarMeasure :
    (sourceKPAdelicStandardHaar K).IsAddHaarMeasure := by
  have : SFinite (sourceKPArchStandardHaar K) := inferInstance
  have : SFinite (sourceKPFiniteStandardHaar K) := inferInstance
  exact AddEquiv.isAddHaarMeasure_map _ (sourceKPAdelicMixedAddEquiv K).symm
    (sourceKPAdelicMixedAddEquiv_symm_continuous K)
    (sourceKPAdelicMixedAddEquiv_continuous K)

theorem sourceKPAdelicStandardHaar_fundamentalDomain :
    sourceKPAdelicStandardHaar K (sourceKPAdelicFundamentalDomain K) = 1 := by
  rw [sourceKPAdelicStandardHaar, Measure.map_apply
    (sourceKPAdelicMixedAddEquiv_symm_continuous K).measurable
    (sourceKPAdelicFundamentalDomain_measurable K)]
  have he : (sourceKPAdelicMixedAddEquiv K).symm ⁻¹'
      sourceKPAdelicFundamentalDomain K =
      ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis K) ×ˢ
        (IntegralAdeles.Construction.finiteIntegralRing K : Set 𝔸ᶠ[K]) := by
    ext a
    change (InfiniteAdeleRing.ringEquiv_mixedSpace K
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm a.1) ∈ _ ∧ a.2 ∈ _) ↔ _
    rw [RingEquiv.apply_symm_apply]
    rfl
  rw [he, Measure.prod_prod, sourceKPArchStandardHaar_fundamentalDomain,
    sourceKPFiniteStandardHaar_integral]
  exact ENNReal.mul_inv_cancel (sourceKPDiscriminantRoot_ne_zero K)
    (sourceKPDiscriminantRoot_ne_top K)

theorem sourceKPAdelicStandardHaar_fundamentalDomain_pos :
    0 < sourceKPAdelicStandardHaar K (sourceKPAdelicFundamentalDomain K) := by
  rw [sourceKPAdelicStandardHaar_fundamentalDomain]
  exact zero_lt_one

end
end ArtinMatthews
