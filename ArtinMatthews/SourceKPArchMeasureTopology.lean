module

public import ArtinMatthews.SourceKPArchComponent
public import ArtinMatthews.SourceKPFiniteLevelTopology
public import ArtinMatthews.SourceAdelicRationalTopology
public import ArtinMatthews.SourceAdelicSecondCountable
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

/-! The measurable archimedean group and the literal left arithmetic quotient. -/
namespace ArtinMatthews
open NumberField Matrix MeasureTheory
open scoped NumberField MatrixGroups AdeleRing Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]

instance sourceKPArchMeasure_secondCountable :
    SecondCountableTopology (PGL(2, InfiniteAdeleRing K)) := by
  have : SecondCountableTopology (InfiniteAdeleRing K) := by
    change SecondCountableTopology ((v : InfinitePlace K) → v.Completion)
    infer_instance
  have : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → InfiniteAdeleRing K))
  have : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) ≃ₜ
      (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))ᵐᵒᵖ).symm.isEmbedding.secondCountableTopology
  have : SecondCountableTopology (GL (Fin 2) (InfiniteAdeleRing K)) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  exact Topology.IsOpenQuotientMap.secondCountableTopology
    (QuotientGroup.isOpenQuotientMap_mk
      (N := Subgroup.center (GL (Fin 2) (InfiniteAdeleRing K))))

instance sourceKPArchMeasure_measurableSpace : MeasurableSpace (PGL(2, InfiniteAdeleRing K)) :=
  borel _

instance sourceKPArchMeasure_borelSpace : BorelSpace (PGL(2, InfiniteAdeleRing K)) := ⟨rfl⟩

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

instance sourceKPArchComponentSubgroup_countable (b : SourceKPFiniteLevelFiber K hζ) :
    Countable (sourceKPArchComponentSubgroup K hζ b) := by
  have : Countable (Matrix (Fin 2) (Fin 2) K) :=
    inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  have : Countable (GL (Fin 2) K) := Units.val_injective.countable
  have hq : Function.Surjective (QuotientGroup.mk : GL (Fin 2) K → PGL(2, K)) :=
    QuotientGroup.mk_surjective
  have : Countable (PGL(2, K)) := hq.countable
  apply Set.Countable.to_subtype
  change ((sourceKPRationalArchMap K hζ) ''
    (sourceKPRationalFiniteStabilizer K hζ b : Set (PGL(2, K)))).Countable
  exact (Set.to_countable _).image _

abbrev SourceKPArchComponentQuotient (b : SourceKPFiniteLevelFiber K hζ) :=
  Quotient (QuotientGroup.rightRel (sourceKPArchComponentSubgroup K hζ b))

def sourceKPArchComponentQuotientMap (b : SourceKPFiniteLevelFiber K hζ) :
    PGL(2, InfiniteAdeleRing K) → SourceKPArchComponentQuotient K hζ b :=
  Quotient.mk (QuotientGroup.rightRel (sourceKPArchComponentSubgroup K hζ b))

theorem sourceKPArchComponentQuotientMap_measurable (b : SourceKPFiniteLevelFiber K hζ) :
    Measurable (sourceKPArchComponentQuotientMap K hζ b) :=
  measurable_quotient_mk' (s := QuotientGroup.rightRel (sourceKPArchComponentSubgroup K hζ b))

theorem sourceKPArchComponentQuotientMap_continuous (b : SourceKPFiniteLevelFiber K hζ) :
    Continuous (sourceKPArchComponentQuotientMap K hζ b) := continuous_quot_mk

theorem sourceKPArchComponentQuotientMap_smul (b : SourceKPFiniteLevelFiber K hζ)
    (γ : sourceKPArchComponentSubgroup K hζ b) (g : PGL(2, InfiniteAdeleRing K)) :
    sourceKPArchComponentQuotientMap K hζ b (γ • g) =
      sourceKPArchComponentQuotientMap K hζ b g := by
  apply Quotient.sound
  exact ⟨γ, rfl⟩

end
end ArtinMatthews
