module

public import ArtinMatthews.FiniteIsotropyChartMeasure
public import ArtinMatthews.SourceKPUpperQuotientMeasure
public import ArtinMatthews.FiniteIsotropyProjectionMeasure
public import ArtinMatthews.SourceKPArithmeticDiscreteness
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Dynamics.Ergodic.Action.Regular
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

/-! Actual finite-isotropy hyperbolic charts retain their full stabilizer weight. -/
namespace ArtinMatthews
open NumberField Matrix MeasureTheory Topology
open scoped NumberField MatrixGroups AdeleRing Classical ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPArithmeticUpperMeasure_slice (b : SourceKPFiniteLevelFiber K hζ)
    (H : Subgroup (sourceKPArchComponentSubgroup K hζ b)) [Finite H]
    (U : Set (SourceKPArchUpperHalfSpace K)) (hU : MeasurableSet U)
    (himage : MeasurableSet (Quotient.mk
      (MulAction.orbitRel (sourceKPArchComponentSubgroup K hζ b) (SourceKPArchUpperHalfSpace K)) '' U))
    (hstable : ∀ h : H, ∀ x ∈ U, (h : sourceKPArchComponentSubgroup K hζ b) • x ∈ U)
    (hsep : ∀ γ : sourceKPArchComponentSubgroup K hζ b, ∀ x ∈ U, γ • x ∈ U → γ ∈ H) :
    (sourceKPArithmeticUpperMeasure K hζ b).restrict (Quotient.mk _ '' U) =
      (Nat.card H : ℝ≥0∞)⁻¹ • ((sourceKPArchHyperbolicMeasure K).restrict U).map (Quotient.mk _) := by
  exact sourceFiniteSlice_projection_measure (sourceKPArchHaar K hζ)
    (sourceKPArchComponentQuotientMeasure K hζ b (sourceKPArchHaar K hζ))
    (sourceKPArchHyperbolicMeasure K) (sourceKPUpperProjection K hζ)
    (sourceKPUpperProjection_preserving K hζ) (sourceKPUpperProjection_equivariant K hζ b)
    (sourceKPUpperQuotientProjection K hζ b) (sourceKPUpperQuotientProjection_measurable K hζ b)
    (sourceKPUpperQuotientProjection_mk K hζ b) H
    (sourceKPArchComponentFundamentalDomain_isFundamental K hζ b (sourceKPArchHaar K hζ))
    U hU himage hstable hsep


variable (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K)
    (c : SourceFiniteIsotropyChart (sourceKPArchComponentSubgroup K hζ b)
      (SourceKPArchUpperHalfSpace K) p)

theorem sourceKPUpperChart_measurePreserving :
    MeasurePreserving (sourceFiniteChartProjection c)
      ((Nat.card (MulAction.stabilizer (sourceKPArchComponentSubgroup K hζ b) p) : ℝ≥0∞)⁻¹ •
        sourceFiniteChartDomainMeasure c (sourceKPArchHyperbolicMeasure K))
      ((sourceKPArithmeticUpperMeasure K hζ b).restrict
        (Set.range (sourceFiniteChartProjection c))) :=
  sourceFiniteChartProjection_measurePreserving (sourceKPArchHaar K hζ)
    (sourceKPArchComponentQuotientMeasure K hζ b (sourceKPArchHaar K hζ))
    (sourceKPArchHyperbolicMeasure K) (sourceKPUpperProjection K hζ)
    (sourceKPUpperProjection_preserving K hζ) (sourceKPUpperProjection_equivariant K hζ b)
    (sourceKPUpperQuotientProjection K hζ b) (sourceKPUpperQuotientProjection_measurable K hζ b)
    (sourceKPUpperQuotientProjection_mk K hζ b)
    (sourceKPArchComponentFundamentalDomain_isFundamental K hζ b (sourceKPArchHaar K hζ)) c

include c in
theorem sourceKPUpperChart_weight_pos :
    0 < (Nat.card (MulAction.stabilizer (sourceKPArchComponentSubgroup K hζ b) p) : ℝ≥0∞)⁻¹ ∧
      (Nat.card (MulAction.stabilizer (sourceKPArchComponentSubgroup K hζ b) p) : ℝ≥0∞)⁻¹ ≠ ⊤ :=
  sourceFiniteChart_weight_pos c


instance sourceKPUpperChartDomain_finite :
    IsFiniteMeasure (sourceFiniteChartDomainMeasure c (sourceKPArchHyperbolicMeasure K)) where
  measure_univ_lt_top := by
    change (sourceKPArchHyperbolicMeasure K).comap
      (Subtype.val : ↥(c.domain : Set (SourceKPArchUpperHalfSpace K)) →
        SourceKPArchUpperHalfSpace K) Set.univ < ⊤
    rw [comap_subtype_coe_apply (s := (c.domain : Set (SourceKPArchUpperHalfSpace K)))
      c.isOpen_domain.measurableSet]
    simp only [Set.image_univ, Subtype.range_coe]
    exact (measure_mono (subset_closure : (c.domain : Set (SourceKPArchUpperHalfSpace K)) ⊆
      closure (c.domain : Set (SourceKPArchUpperHalfSpace K)))).trans_lt
        c.isCompact_closure.measure_lt_top

end
end ArtinMatthews
