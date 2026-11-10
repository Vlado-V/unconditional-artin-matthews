module

public import ArtinMatthews.SourceKPTranslateCompactLevel
public import ArtinMatthews.SourceKPAutomorphicParametricContinuity
public import ArtinMatthews.SourceKPCuspRepresentativeHaar
public import ArtinMatthews.SourceKPArithmeticDiscreteness
public import ArtinMatthews.SourceKPCompactRationalTransport
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
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.Separation.Lemmas
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Haar times counting measure on the actual common-level representatives. -/
namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory Set
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "A" => PGL(2, InfiniteAdeleRing K)
local notation "Γ" => PGL(2, K)
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "F" => SourceKPFiniteLevelFiber K hζ
local notation "X" => SourceKPFiniteLevelSpace K hζ
local notation "D" => sourceKPFiniteLevelConjugate K hζ
local notation "μA" => sourceKPArchHaar K hζ

abbrev SourceKPTranslateRepresentativeSpace (T : Finset Gf) :=
  A × SourceKPTranslateFiniteLevelFiber K hζ T

variable (T : Finset (SourceKPFiniteAdeleProjective K hζ))
include T

local notation "J" => sourceKPFiniteTranslateLevel K hζ T
local notation "FJ" => SourceKPTranslateFiniteLevelFiber K hζ T
local notation "XJ" => SourceKPTranslateRepresentativeSpace K hζ T
local notation "YJ" => SourceKPTranslateAutomorphicCompactLevel K hζ T

instance sourceKPTranslateFiniteLevelFiber_measurable : MeasurableSpace FJ := borel _
instance sourceKPTranslateFiniteLevelFiber_borel : BorelSpace FJ := ⟨rfl⟩

instance sourceKPTranslateFiniteLevelFiber_countable : Countable FJ := by
  let h := sourceKPFiniteTranslateLevel_le_conjugate_one K hζ T
  let : ((J).subgroupOf (D 1)).FiniteIndex := Subgroup.isFiniteRelIndex_iff_finiteIndex.mp
    (sourceKPFiniteTranslateLevel_finiteRelIndex_conjugate K hζ T 1)
  exact (sourceKPFiniteRightTranslateProductEquiv K hζ T 1 h).injective.countable

instance sourceKPTranslateRepresentative_rationalAction : MulAction Γ XJ where
  smul γ x := (sourceKPRationalArchMap K hζ γ * x.1, sourceKPRationalFiniteMap K hζ γ • x.2)
  one_smul x := by
    apply Prod.ext
    · change sourceKPRationalArchMap K hζ 1 * x.1 = x.1
      rw [map_one, one_mul]
    · change sourceKPRationalFiniteMap K hζ 1 • x.2 = x.2
      rw [map_one, one_smul]
  mul_smul γ δ x := by
    apply Prod.ext
    · change sourceKPRationalArchMap K hζ (γ * δ) * x.1 =
        sourceKPRationalArchMap K hζ γ * (sourceKPRationalArchMap K hζ δ * x.1)
      rw [map_mul, mul_assoc]
    · change sourceKPRationalFiniteMap K hζ (γ * δ) • x.2 =
        sourceKPRationalFiniteMap K hζ γ • (sourceKPRationalFiniteMap K hζ δ • x.2)
      rw [map_mul, mul_smul]

def sourceKPTranslateRepresentativeHaar : Measure XJ :=
  (μA).prod Measure.count

theorem sourceKPTranslateFiniteCount_preserving (g : Gf) :
    MeasurePreserving (fun b : FJ => g • b) Measure.count Measure.count := by
  let e : Equiv.Perm FJ := MulAction.toPerm g
  have hem : Measurable (e : FJ → FJ) := continuous_of_discreteTopology.measurable
  refine ⟨hem, ?_⟩
  change Measure.map (e : FJ → FJ) Measure.count = Measure.count
  ext U hU
  rw [Measure.map_apply hem hU, Measure.count_apply (hU.preimage hem), Measure.count_apply hU]
  rw [← e.injective.encard_image, Set.image_preimage_eq _ e.surjective]

theorem sourceKPTranslateRepresentativeHaar_rational (γ : Γ) :
    MeasurePreserving (fun x : XJ => γ • x)
      (sourceKPTranslateRepresentativeHaar K hζ T) (sourceKPTranslateRepresentativeHaar K hζ T) :=
  (sourceKPArchHaar_left_preserving K hζ (sourceKPRationalArchMap K hζ γ)).prod
    (sourceKPTranslateFiniteCount_preserving K hζ T (sourceKPRationalFiniteMap K hζ γ))

instance sourceKPTranslateRepresentative_rationalMeasurable : MeasurableConstSMul Γ XJ where
  measurable_const_smul γ := (sourceKPTranslateRepresentativeHaar_rational K hζ T γ).measurable

instance sourceKPTranslateRepresentativeHaar_rationalInvariant :
    SMulInvariantMeasure Γ XJ (sourceKPTranslateRepresentativeHaar K hζ T) where
  measure_preimage_smul := by
    intro γ S hS
    have h := sourceKPTranslateRepresentativeHaar_rational K hζ T γ
    rw [← Measure.map_apply h.measurable hS, h.map_eq]

def sourceKPTranslateRepresentativeMap (t : Gf) (h : J ≤ D t) : XJ → X :=
  Prod.map id (sourceKPFiniteRightTranslateMap K hζ T t h)

theorem sourceKPFiniteRightTranslateMap_measurable (t : Gf) (h : J ≤ D t) :
    Measurable (sourceKPFiniteRightTranslateMap K hζ T t h) :=
  continuous_of_discreteTopology.measurable

theorem sourceKPTranslateRepresentativeMap_measurable (t : Gf) (h : J ≤ D t) :
    Measurable (sourceKPTranslateRepresentativeMap K hζ T t h) :=
  measurable_id.prodMap (sourceKPFiniteRightTranslateMap_measurable K hζ T t h)

theorem sourceKPTranslateRepresentativeMap_rational (t : Gf) (h : J ≤ D t) (γ : Γ) (x : XJ) :
    sourceKPTranslateRepresentativeMap K hζ T t h (γ • x) =
      γ • sourceKPTranslateRepresentativeMap K hζ T t h x :=
  Prod.ext rfl (sourceKPFiniteRightTranslateMap_smul K hζ T t h (sourceKPRationalFiniteMap K hζ γ) x.2)

theorem sourceKPFiniteRightTranslateMap_count (t : Gf) (h : J ≤ D t) :
    Measure.map (sourceKPFiniteRightTranslateMap K hζ T t h) Measure.count =
      ((J).relIndex (D t) : ℝ≥0∞) • (Measure.count : Measure F) := by
  apply Measure.ext_of_singleton
  intro b
  let S := (sourceKPFiniteRightTranslateMap K hζ T t h) ⁻¹' {b}
  have hS : S.Finite := sourceKPFiniteRightTranslateFiber_finite K hζ T t h b
  have hc : Nat.card S = (J).relIndex (D t) :=
    sourceKPFiniteRightTranslateFiber_card K hζ T t h b
  rw [Measure.map_apply (sourceKPFiniteRightTranslateMap_measurable K hζ T t h)
      (measurableSet_singleton b), Measure.count_apply_finite _ hS,
    ← Nat.card_eq_card_finite_toFinset hS, hc, Measure.smul_apply,
    Measure.count_singleton, smul_eq_mul, mul_one]

theorem sourceKPTranslateRepresentativeMap_haar (t : Gf) (h : J ≤ D t) :
    Measure.map (sourceKPTranslateRepresentativeMap K hζ T t h)
      (sourceKPTranslateRepresentativeHaar K hζ T) =
        ((J).relIndex (D t) : ℝ≥0∞) • sourceKPFiniteRepresentativeHaar K hζ := by
  rw [sourceKPTranslateRepresentativeMap, sourceKPTranslateRepresentativeHaar,
    sourceKPFiniteRepresentativeHaar, ← Measure.map_prod_map μA (Measure.count : Measure FJ)
      measurable_id (sourceKPFiniteRightTranslateMap_measurable K hζ T t h),
    Measure.map_id, sourceKPFiniteRightTranslateMap_count, Measure.prod_smul_right]

def sourceKPTranslateRepresentativeToCompact (x : XJ) : YJ :=
  sourceKPTranslateUpperMk K hζ T
    (sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk x.1), x.2)

theorem sourceKPTranslateRepresentativeToCompact_measurable :
    Measurable (sourceKPTranslateRepresentativeToCompact K hζ T) := by
  let : SecondCountableTopology FJ := DiscreteTopology.secondCountableTopology_of_countable
  have ha : Continuous (fun a : A => sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk a)) :=
    (sourceKPArchSymmetricHomeomorph K hζ).continuous.comp QuotientGroup.continuous_mk
  exact ((sourceKPTranslateUpperMk_isOpenQuotientMap K hζ T).continuous.comp
    ((ha.comp continuous_fst).prodMk continuous_snd)).measurable

theorem sourceKPTranslateRepresentativeToCompact_rational (γ : Γ) (x : XJ) :
    sourceKPTranslateRepresentativeToCompact K hζ T (γ • x) =
      sourceKPTranslateRepresentativeToCompact K hζ T x := by
  apply Quotient.sound
  apply MulAction.mem_orbit_iff.mpr
  refine ⟨γ, Prod.ext ?_ rfl⟩
  exact (sourceKPArchSymmetricHomeomorph_smul K hζ (sourceKPRationalArchMap K hζ γ)
    (QuotientGroup.mk x.1)).symm

theorem sourceKPTranslateCompactMap_comp_representative (t : Gf) (h : J ≤ D t) :
    (sourceKPTranslateAutomorphicCompactMap K hζ T t h) ∘
      (sourceKPTranslateRepresentativeToCompact K hζ T) =
        (sourceKPFiniteLevelToCompact K hζ) ∘ (sourceKPTranslateRepresentativeMap K hζ T t h) := by
  funext x
  rw [Function.comp_apply, Function.comp_apply, sourceKPTranslateRepresentativeToCompact,
    sourceKPTranslateAutomorphicCompactMap_upperMk]
  exact sourceKPUpperToCompact_mk K hζ
    (sourceKPFiniteRightTranslateMap K hζ T t h x.2) x.1

end
end ArtinMatthews
