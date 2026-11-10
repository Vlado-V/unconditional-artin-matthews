module

public import ArtinMatthews.SourceKPAdelicOutgoingContinuationSection
public import ArtinMatthews.SourceKPAdelicOutgoingExceptionalTrace
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

/-! Literal relations in the actual continued negative principal series. -/
namespace ArtinMatthews
open NumberField
open scoped NumberField AdeleRing MatrixGroups Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "E" => sourceKPAdelicOutgoingExceptionalSection K hζ
local notation "G" => SourceKPAdelicProjective K hζ
local notation "Π₋" => SourceKPAdelicPrincipalSeries K hζ (-(1/6 : ℂ))
local notation "ρ₋" => sourceKPAdelicPrincipalSeriesRepresentation K hζ (-(1/6 : ℂ))

variable {I : Type} [Fintype I]

def SourceKPResidualOutgoingRelation (t : I → Gf) (c : I → ℂ) : Prop :=
  (∑ i : I, c i • ρ₋ ((1,t i) : G) E) = (0 : Π₋)

theorem sourceKPResidualOutgoingRelation_iff (t : I → Gf) (c : I → ℂ) :
    SourceKPResidualOutgoingRelation K hζ t c ↔ (∑ i : I, c i • ρ₋ ((1,t i) : G) E) = (0 : Π₋) :=
  Iff.rfl

theorem sourceKPResidualOutgoingRelation_scattering_zero
    (t : I → Gf) (c : I → ℂ) (hrel : SourceKPResidualOutgoingRelation K hζ t c) (qf : Gf) :
    (∑ i : I, c i * sourceKPFiniteFiberScatteringResidue K hζ (qf*t i)
      (sourceKPAdelicOutgoingScatteringWindow K hζ (qf*t i))) = 0 := by
  exact sourceKPAdelicOutgoingExceptionalSection_canonical_scattering_relation K hζ t c hrel qf

end
end ArtinMatthews
