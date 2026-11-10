module

public import ArtinMatthews.SourceKPHeightBandReduction
public import ArtinMatthews.SourceKPFiniteHeightNormalization
public import ArtinMatthews.SourceKPHeightBandCompact
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Finiteness of the actual rational finite-level orbit index. -/

namespace ArtinMatthews
open NumberField Matrix Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPFiniteOrbit_height_band_image_eq_univ (v₀ : InfinitePlace K) :
    (sourceKPAutomorphicFiniteOrbit K hζ) ''
      sourceKPCompactAutomorphicContainer K hζ (sourceKPHeightBandMatrices K hζ v₀ 0 0) =
        Set.univ := by
  apply Set.eq_univ_of_forall
  intro o
  obtain ⟨q, hq, ho⟩ := sourceKPFiniteOrbit_height_one_rep K hζ v₀ o
  obtain ⟨g, hg⟩ := ProjGenLinGroup.mk_surjective (sourceKPAdelicProjectiveProjection K hζ q)
  have hheight : sourceKPAdelicHeight K hζ g = 1 := by
    change sourceKPAdelicHeightOnProjective K hζ (sourceKPAdelicProjectiveProjection K hζ q) = 1 at hq
    rwa [← hg, sourceKPAdelicHeightOnProjective_mk] at hq
  refine ⟨sourceKPAutomorphicLevelMk K hζ q, ?_, ho⟩
  apply sourceKPHeightBand_cover_reduction K hζ v₀ 0 0 q g hg.symm
  simp [hheight]

instance sourceKPFiniteOrbit_finite : Finite (SourceKPFiniteOrbit K hζ) := by
  obtain ⟨v₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
  have h := sourceKPHeightBand_finite_components K hζ v₀ 0 0
  rw [sourceKPFiniteOrbit_height_band_image_eq_univ K hζ v₀] at h
  exact Set.finite_univ_iff.mp h

end
end ArtinMatthews
