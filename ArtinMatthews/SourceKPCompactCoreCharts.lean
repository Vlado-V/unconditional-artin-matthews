module

public import ArtinMatthews.FiniteIsotropyChart
public import ArtinMatthews.SourceKPArithmeticUpperQuotient
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

/-! Finite precompact orbifold chart covers of actual compact height cores. -/
namespace ArtinMatthews
open NumberField Matrix Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPArithmeticUpperComponentMap (b : SourceKPFiniteLevelFiber K hζ)
    (x : SourceKPArithmeticUpperQuotient K hζ b) : SourceKPAutomorphicCompactLevel K hζ :=
  (sourceKPArithmeticUpperComponentHomeomorph K hζ b x).val

theorem sourceKPArithmeticUpperComponentMap_isOpenEmbedding (b : SourceKPFiniteLevelFiber K hζ) :
    IsOpenEmbedding (sourceKPArithmeticUpperComponentMap K hζ b) := by
  have ho : IsOpen ((sourceKPAutomorphicCompactFiniteOrbit K hζ) ⁻¹'
      {sourceKPFiniteOrbitMk K hζ b}) :=
    (isOpen_discrete _).preimage (sourceKPAutomorphicCompactFiniteOrbit_continuous K hζ)
  exact ho.isOpenEmbedding_subtypeVal.comp
    (sourceKPArithmeticUpperComponentHomeomorph K hζ b).isOpenEmbedding

def sourceKPUpperToCompact (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K) :
    SourceKPAutomorphicCompactLevel K hζ :=
  sourceKPArithmeticUpperComponentMap K hζ b (Quotient.mk _ p)

theorem sourceKPUpperToCompact_continuous (b : SourceKPFiniteLevelFiber K hζ) :
    Continuous (sourceKPUpperToCompact K hζ b) :=
  (sourceKPArithmeticUpperComponentMap_isOpenEmbedding K hζ b).continuous.comp continuous_quot_mk

theorem sourceKPUpperToCompact_isOpenMap (b : SourceKPFiniteLevelFiber K hζ) :
    IsOpenMap (sourceKPUpperToCompact K hζ b) :=
  (sourceKPArithmeticUpperComponentMap_isOpenEmbedding K hζ b).isOpenMap.comp
    isOpenMap_quotient_mk'_mul

def sourceKPUpperFiniteChart (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K) :
    SourceFiniteIsotropyChart (sourceKPArchComponentSubgroup K hζ b) (SourceKPArchUpperHalfSpace K) p := by
  let : LocallyCompactSpace (SourceKPArchUpperHalfSpace K) :=
    (sourceKPArchSymmetricHomeomorph K hζ).locallyCompactSpace_iff.mp inferInstance
  let : T2Space (SourceKPArchUpperHalfSpace K) :=
    T2Space.of_injective_continuous (sourceKPArchSymmetricHomeomorph K hζ).symm.injective
      (sourceKPArchSymmetricHomeomorph K hζ).symm.continuous
  exact sourceFiniteIsotropyChartAt (sourceKPArchComponentSubgroup K hζ b) (SourceKPArchUpperHalfSpace K) p

def sourceKPFiniteChartProjection (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K)
    (x : (sourceKPUpperFiniteChart K hζ b p).domain) : SourceKPAutomorphicCompactLevel K hζ :=
  sourceKPUpperToCompact K hζ b x.val

def sourceKPFiniteChartRangeMap (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K) :
    (sourceKPUpperFiniteChart K hζ b p).domain → Set.range (sourceKPFiniteChartProjection K hζ b p) :=
  Set.rangeFactorization (sourceKPFiniteChartProjection K hζ b p)

theorem sourceKPFiniteChartProjection_continuous (b : SourceKPFiniteLevelFiber K hζ)
    (p : SourceKPArchUpperHalfSpace K) : Continuous (sourceKPFiniteChartProjection K hζ b p) :=
  (sourceKPUpperToCompact_continuous K hζ b).comp continuous_subtype_val

theorem sourceKPFiniteChartProjection_isOpenMap (b : SourceKPFiniteLevelFiber K hζ)
    (p : SourceKPArchUpperHalfSpace K) : IsOpenMap (sourceKPFiniteChartProjection K hζ b p) :=
  (sourceKPUpperToCompact_isOpenMap K hζ b).comp
    (sourceKPUpperFiniteChart K hζ b p).isOpen_domain.isOpenEmbedding_subtypeVal.isOpenMap

theorem sourceKPFiniteChartRangeMap_eq_iff (b : SourceKPFiniteLevelFiber K hζ)
    (p : SourceKPArchUpperHalfSpace K) (x y : (sourceKPUpperFiniteChart K hζ b p).domain) :
    sourceKPFiniteChartRangeMap K hζ b p x = sourceKPFiniteChartRangeMap K hζ b p y ↔
      MulAction.orbitRel (MulAction.stabilizer (sourceKPArchComponentSubgroup K hζ b) p)
        (sourceKPUpperFiniteChart K hζ b p).domain x y := by
  constructor
  · intro hxy
    have hval : sourceKPFiniteChartProjection K hζ b p x =
        sourceKPFiniteChartProjection K hζ b p y :=
      congrArg (fun z : Set.range (sourceKPFiniteChartProjection K hζ b p) => z.val) hxy
    have h := (sourceKPArithmeticUpperComponentMap_isOpenEmbedding K hζ b).injective hval
    exact (sourceFiniteChartRangeMap_eq_iff (sourceKPUpperFiniteChart K hζ b p) x y).mp
      (Subtype.ext h)
  · intro hxy
    have h := congrArg Subtype.val
      ((sourceFiniteChartRangeMap_eq_iff (sourceKPUpperFiniteChart K hζ b p) x y).mpr hxy)
    exact Subtype.ext (congrArg (sourceKPArithmeticUpperComponentMap K hζ b) h)

theorem sourceKPFiniteChartRangeMap_isOpenQuotientMap (b : SourceKPFiniteLevelFiber K hζ)
    (p : SourceKPArchUpperHalfSpace K) : IsOpenQuotientMap (sourceKPFiniteChartRangeMap K hζ b p) := by
  refine ⟨?_,?_,?_⟩
  · rintro ⟨y,⟨x,rfl⟩⟩
    exact ⟨x,rfl⟩
  · exact (sourceKPFiniteChartProjection_continuous K hζ b p).subtype_mk _
  · exact (sourceKPFiniteChartProjection_isOpenMap K hζ b p).subtype_mk _

def sourceKPFiniteChartHomeomorph (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K) :
    Quotient (MulAction.orbitRel (MulAction.stabilizer (sourceKPArchComponentSubgroup K hζ b) p)
      (sourceKPUpperFiniteChart K hζ b p).domain) ≃ₜ Set.range (sourceKPFiniteChartProjection K hζ b p) :=
  sourceQuotientHomeomorph _
    ⟨sourceKPFiniteChartRangeMap K hζ b p,
      (sourceKPFiniteChartRangeMap_isOpenQuotientMap K hζ b p).continuous⟩
    (sourceKPFiniteChartRangeMap_isOpenQuotientMap K hζ b p).isQuotientMap
    (fun x y => (sourceKPFiniteChartRangeMap_eq_iff K hζ b p x y).symm)

@[simp] theorem sourceKPFiniteChartHomeomorph_mk (b : SourceKPFiniteLevelFiber K hζ)
    (p : SourceKPArchUpperHalfSpace K) (x : (sourceKPUpperFiniteChart K hζ b p).domain) :
    (sourceKPFiniteChartHomeomorph K hζ b p (Quotient.mk _ x) : SourceKPAutomorphicCompactLevel K hζ) =
      sourceKPUpperToCompact K hζ b x.val := rfl

theorem sourceKPFiniteChart_range_open (b : SourceKPFiniteLevelFiber K hζ)
    (p : SourceKPArchUpperHalfSpace K) : IsOpen (Set.range (sourceKPFiniteChartProjection K hζ b p)) :=
  (sourceKPFiniteChartProjection_isOpenMap K hζ b p).isOpen_range

theorem sourceKPUpperToCompact_mem_chart (b : SourceKPFiniteLevelFiber K hζ)
    (p : SourceKPArchUpperHalfSpace K) :
    sourceKPUpperToCompact K hζ b p ∈ Set.range (sourceKPFiniteChartProjection K hζ b p) :=
  ⟨⟨p,(sourceKPUpperFiniteChart K hζ b p).center_mem⟩,rfl⟩

theorem sourceKPUpperToCompact_cover (x : SourceKPAutomorphicCompactLevel K hζ) :
    ∃ (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K),
      sourceKPUpperToCompact K hζ b p = x := by
  induction x using Quotient.inductionOn with
  | _ x =>
    obtain ⟨q,rfl⟩ := sourceKPAutomorphicLevelMk_surjective K hζ x
    let b : SourceKPFiniteLevelFiber K hζ := QuotientGroup.mk q.2
    refine ⟨b,sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk q.1),?_⟩
    exact sourceKPArithmeticUpperComponentHomeomorph_mk K hζ b q.1

theorem sourceKPCompact_finite_chart_cover (C : Set (SourceKPAutomorphicCompactLevel K hζ))
    (hC : IsCompact C) :
    ∃ I : Finset (SourceKPFiniteLevelFiber K hζ × SourceKPArchUpperHalfSpace K),
      C ⊆ ⋃ i ∈ I, Set.range (sourceKPFiniteChartProjection K hζ i.1 i.2) := by
  apply hC.elim_finite_subcover
    (fun i : SourceKPFiniteLevelFiber K hζ × SourceKPArchUpperHalfSpace K =>
      Set.range (sourceKPFiniteChartProjection K hζ i.1 i.2))
    (fun i => sourceKPFiniteChart_range_open K hζ i.1 i.2)
  intro x _
  obtain ⟨b,p,hp⟩ := sourceKPUpperToCompact_cover K hζ x
  exact Set.mem_iUnion.mpr ⟨(b,p),hp ▸ sourceKPUpperToCompact_mem_chart K hζ b p⟩

end
end ArtinMatthews
