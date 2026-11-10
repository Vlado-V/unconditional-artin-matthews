module

public import ArtinMatthews.FiniteIsotropyChartMeasure
public import ArtinMatthews.SourceKPArchHaar
public import ArtinMatthews.SourceKPAutomorphicL2
public import ArtinMatthews.SourceKPCompactCoreCharts
public import ArtinMatthews.SourceKPGlobalChartMeasure
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

/-! The exact scalar L2 lift from the global automorphic quotient chart. -/
namespace ArtinMatthews
open NumberField MeasureTheory
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K)

def sourceKPFiniteChartLocalMeasure : Measure (sourceKPUpperFiniteChart K hζ b p).domain :=
  (Nat.card (MulAction.stabilizer (sourceKPArchComponentSubgroup K hζ b) p) : ℝ≥0∞)⁻¹ •
    sourceFiniteChartDomainMeasure (sourceKPUpperFiniteChart K hζ b p) (sourceKPArchHyperbolicMeasure K)

def sourceKPFiniteChartQuotientMeasure : Measure (SourceKPAutomorphicCompactLevel K hζ) :=
  (sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)).restrict
    (Set.range (sourceKPFiniteChartProjection K hζ b p))

theorem sourceKPFiniteChartProjection_measured :
    MeasurePreserving (sourceKPFiniteChartProjection K hζ b p)
      (sourceKPFiniteChartLocalMeasure K hζ b p) (sourceKPFiniteChartQuotientMeasure K hζ b p) :=
  sourceKPFiniteChartProjection_measurePreserving K hζ b p

abbrev SourceKPFiniteChartQuotientL2 := Lp ℂ 2 (sourceKPFiniteChartQuotientMeasure K hζ b p)
abbrev SourceKPFiniteChartLiftedL2 := Lp ℂ 2 (sourceKPFiniteChartLocalMeasure K hζ b p)

def sourceKPFiniteChartL2Pullback :
    SourceKPFiniteChartQuotientL2 K hζ b p →ₗᵢ[ℂ] SourceKPFiniteChartLiftedL2 K hζ b p :=
  Lp.compMeasurePreservingₗᵢ ℂ (sourceKPFiniteChartProjection K hζ b p)
    (sourceKPFiniteChartProjection_measured K hζ b p)

theorem sourceKPFiniteChartL2Pullback_coe (f : SourceKPFiniteChartQuotientL2 K hζ b p) :
    (sourceKPFiniteChartL2Pullback K hζ b p f : (sourceKPUpperFiniteChart K hζ b p).domain → ℂ)
      =ᵐ[sourceKPFiniteChartLocalMeasure K hζ b p]
        fun x => f (sourceKPFiniteChartProjection K hζ b p x) :=
  Lp.coeFn_compMeasurePreserving f (sourceKPFiniteChartProjection_measured K hζ b p)

theorem sourceKPFiniteChartL2Pullback_norm (f : SourceKPFiniteChartQuotientL2 K hζ b p) :
    ‖sourceKPFiniteChartL2Pullback K hζ b p f‖ = ‖f‖ :=
  (sourceKPFiniteChartL2Pullback K hζ b p).norm_map f

theorem sourceKPFiniteChartL2Pullback_injective :
    Function.Injective (sourceKPFiniteChartL2Pullback K hζ b p) :=
  (sourceKPFiniteChartL2Pullback K hζ b p).injective

theorem sourceKPFiniteChartLocalMeasure_weight :
    0 < (Nat.card (MulAction.stabilizer (sourceKPArchComponentSubgroup K hζ b) p) : ℝ≥0∞)⁻¹ ∧
      (Nat.card (MulAction.stabilizer (sourceKPArchComponentSubgroup K hζ b) p) : ℝ≥0∞)⁻¹ ≠ ⊤ :=
  sourceFiniteChart_weight_pos (sourceKPUpperFiniteChart K hζ b p)

end
end ArtinMatthews
