module

public import ArtinMatthews.SourceKPHeightBandReduction
public import ArtinMatthews.SourceKPAdelicBaseCompactTopology
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

namespace ArtinMatthews
open NumberField Matrix Topology
open scoped NumberField MatrixGroups AdeleRing Pointwise
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPHeightBandMatrices_isCompact (v₀ : InfinitePlace K) (a b : ℝ) :
    IsCompact (sourceKPHeightBandMatrices K hζ v₀ a b) :=
  (sourceKPAdelicBorelBand_isCompact K hζ v₀ a b).mul
    (SourceKPAdelicBaseCompactMatrix_isCompact K hζ)

theorem sourceKPHeightBand_automorphic_container_isCompact
    (v₀ : InfinitePlace K) (a b : ℝ) :
    IsCompact (sourceKPCompactAutomorphicContainer K hζ
      (sourceKPHeightBandMatrices K hζ v₀ a b)) :=
  sourceKPCompactAutomorphicContainer_isCompact K hζ _
    (sourceKPHeightBandMatrices_isCompact K hζ v₀ a b)

theorem sourceKPHeightBand_compact_container (v₀ : InfinitePlace K) (a b : ℝ) :
    ∃ C : Set (SourceKPAutomorphicLevel K hζ), IsCompact C ∧
      ∀ (q : SourceKPAdelicProjective K hζ) (g : GL (Fin 2) 𝔸[K]),
        sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g →
        Real.log (sourceKPAdelicHeight K hζ g) ∈ Set.Icc a b →
          sourceKPAutomorphicLevelMk K hζ q ∈ C := by
  refine ⟨sourceKPCompactAutomorphicContainer K hζ
    (sourceKPHeightBandMatrices K hζ v₀ a b),
      sourceKPHeightBand_automorphic_container_isCompact K hζ v₀ a b,?_⟩
  exact sourceKPHeightBand_cover_reduction K hζ v₀ a b

theorem sourceKPHeightBand_finite_components (v₀ : InfinitePlace K) (a b : ℝ) :
    Set.Finite ((sourceKPAutomorphicFiniteOrbit K hζ) ''
      sourceKPCompactAutomorphicContainer K hζ (sourceKPHeightBandMatrices K hζ v₀ a b)) :=
  sourceKPCompactAutomorphicContainer_finite_components K hζ _
    (sourceKPHeightBandMatrices_isCompact K hζ v₀ a b)

end
end ArtinMatthews
