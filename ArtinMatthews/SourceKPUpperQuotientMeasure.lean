module

public import ArtinMatthews.SourceKPArchHaar
public import ArtinMatthews.SourceKPArithmeticUpperQuotient
public import ArtinMatthews.SourceKPArchComponentMeasure
public import ArtinMatthews.SourceArchHyperbolicRegularity
public import ArtinMatthews.SourceKPArithmeticDiscreteness
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
public import Mathlib.Topology.Algebra.ProperAction.CompactlyGenerated
public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual hyperbolic orbit measure induced by the normalized archimedean Haar measure. -/
namespace ArtinMatthews
open NumberField Matrix MeasureTheory Topology
open scoped NumberField MatrixGroups AdeleRing Classical ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceUpperMeasureSymmetricMeasurable :
    MeasurableSpace (SourceKPArchSymmetricSpace K hζ) := borel _
local instance sourceUpperMeasureSymmetricBorel :
    BorelSpace (SourceKPArchSymmetricSpace K hζ) := ⟨rfl⟩

instance sourceKPUpperQuotient_t2 (b : SourceKPFiniteLevelFiber K hζ) :
    T2Space (SourceKPArithmeticUpperQuotient K hζ b) := by
  have : ProperSMul (sourceKPArchComponentSubgroup K hζ b) (SourceKPArchUpperHalfSpace K) :=
    properlyDiscontinuousSMul_iff_properSMul.mp inferInstance
  change T2Space (Quotient (MulAction.orbitRel (sourceKPArchComponentSubgroup K hζ b)
    (SourceKPArchUpperHalfSpace K)))
  infer_instance

instance sourceKPUpperQuotient_secondCountable (b : SourceKPFiniteLevelFiber K hζ) :
    SecondCountableTopology (SourceKPArithmeticUpperQuotient K hζ b) :=
  Topology.IsOpenQuotientMap.secondCountableTopology
    (show IsOpenQuotientMap (Quotient.mk (MulAction.orbitRel
      (sourceKPArchComponentSubgroup K hζ b) (SourceKPArchUpperHalfSpace K))) from
        MulAction.isOpenQuotientMap_quotientMk)

instance sourceKPUpperQuotient_borel (b : SourceKPFiniteLevelFiber K hζ) :
    BorelSpace (SourceKPArithmeticUpperQuotient K hζ b) := by
  have : PolishSpace {y : ℝ // 0 < y} := (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))).polishSpace
  have : PolishSpace (SourceKPArchUpperHalfSpace K) := inferInstance
  have : SecondCountableTopology (Quotient (MulAction.orbitRel
      (sourceKPArchComponentSubgroup K hζ b) (SourceKPArchUpperHalfSpace K))) :=
    sourceKPUpperQuotient_secondCountable K hζ b
  have : T2Space (Quotient (MulAction.orbitRel
      (sourceKPArchComponentSubgroup K hζ b) (SourceKPArchUpperHalfSpace K))) :=
    sourceKPUpperQuotient_t2 K hζ b
  change BorelSpace (Quotient (MulAction.orbitRel
    (sourceKPArchComponentSubgroup K hζ b) (SourceKPArchUpperHalfSpace K)))
  exact Quotient.borelSpace

def sourceKPUpperProjection (g : PGL(2, InfiniteAdeleRing K)) : SourceKPArchUpperHalfSpace K :=
  sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk g)

theorem sourceKPUpperProjection_continuous : Continuous (sourceKPUpperProjection K hζ) :=
  (sourceKPArchSymmetricHomeomorph K hζ).continuous.comp continuous_quot_mk

theorem sourceKPUpperProjection_preserving :
    MeasurePreserving (sourceKPUpperProjection K hζ)
      (sourceKPArchHaar K hζ) (sourceKPArchHyperbolicMeasure K) :=
  (sourceKPArchSymmetricHomeomorph_measurePreserving K hζ).comp
    (sourceKPArchHaar_projection K hζ)

theorem sourceKPUpperProjection_equivariant (b : SourceKPFiniteLevelFiber K hζ)
    (γ : sourceKPArchComponentSubgroup K hζ b) (g : PGL(2, InfiniteAdeleRing K)) :
    sourceKPUpperProjection K hζ (γ • g) = γ • sourceKPUpperProjection K hζ g := by
  exact sourceKPArithmeticSymmetricToUpper_equivariant K hζ b γ (QuotientGroup.mk g)

def sourceKPUpperQuotientProjection (b : SourceKPFiniteLevelFiber K hζ) :
    SourceKPArchComponentQuotient K hζ b → SourceKPArithmeticUpperQuotient K hζ b :=
  sourceOrbitMap (sourceKPUpperProjection K hζ) (sourceKPUpperProjection_equivariant K hζ b)

@[simp] theorem sourceKPUpperQuotientProjection_mk (b : SourceKPFiniteLevelFiber K hζ)
    (g : PGL(2, InfiniteAdeleRing K)) :
    sourceKPUpperQuotientProjection K hζ b (sourceKPArchComponentQuotientMap K hζ b g) =
      Quotient.mk _ (sourceKPUpperProjection K hζ g) := rfl

theorem sourceKPUpperQuotientProjection_measurable (b : SourceKPFiniteLevelFiber K hζ) :
    Measurable (sourceKPUpperQuotientProjection K hζ b) := by
  intro A hA
  apply measurableSet_quotient.mpr
  exact ((measurable_quotient_mk' (s := MulAction.orbitRel
    (sourceKPArchComponentSubgroup K hζ b) (SourceKPArchUpperHalfSpace K))).comp
      (sourceKPUpperProjection_preserving K hζ).measurable) hA

theorem sourceKPUpperQuotientProjection_component (b : SourceKPFiniteLevelFiber K hζ)
    (q : SourceKPArchComponentQuotient K hζ b) :
    (sourceKPArithmeticUpperComponentHomeomorph K hζ b
      (sourceKPUpperQuotientProjection K hζ b q) : SourceKPAutomorphicCompactLevel K hζ) =
        sourceKPAutomorphicCompactMk K hζ (sourceKPArchComponentEmbedding K hζ b q) := by
  induction q using Quotient.inductionOn with
  | _ g => exact sourceKPArithmeticUpperComponentHomeomorph_mk K hζ b g

def sourceKPArithmeticUpperMeasure (b : SourceKPFiniteLevelFiber K hζ) :
    Measure (SourceKPArithmeticUpperQuotient K hζ b) :=
  (sourceKPArchComponentQuotientMeasure K hζ b (sourceKPArchHaar K hζ)).map
    (sourceKPUpperQuotientProjection K hζ b)


end
end ArtinMatthews
