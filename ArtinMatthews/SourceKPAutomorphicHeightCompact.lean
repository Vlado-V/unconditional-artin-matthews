module

public import ArtinMatthews.SourceAdelicOrbitHeightTopology
public import ArtinMatthews.SourceKPAdelicHeightReduction
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

/-! Compact sublevels of the actual rational-orbit height. Every geometric
input is supplied by the checked actual adelic constructions. -/

namespace ArtinMatthews
open NumberField Matrix Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAutomorphicOrbitHeight_sublevel_isCompact (T : ℝ) :
    IsCompact {x : SourceKPAutomorphicLevel K hζ | sourceKPAutomorphicOrbitHeight K hζ x ≤ T} := by
  obtain ⟨c,hc,hreduce⟩ := sourceKPAdelicCover_rational_height_lower K hζ
  let v₀ : InfinitePlace K := Classical.choice inferInstance
  apply (sourceKPHeightBand_automorphic_container_isCompact K hζ v₀ (Real.log c) (Real.log T)).of_isClosed_subset
    (sourceKPAutomorphicOrbitHeight_sublevel_closed K hζ T)
  intro x hx
  obtain ⟨q,rfl⟩ := sourceKPAutomorphicLevelMk_surjective K hζ x
  change sourceKPAdelicOrbitHeight K hζ q ≤ T at hx
  obtain ⟨γ,hγ⟩ := hreduce q
  let r := sourceKPAdelicProjectiveRationalLift K hζ γ*q
  have hupper : sourceKPAdelicCoverHeight K hζ r ≤ T :=
    (sourceKPAdelicCoverHeight_le_orbit K hζ r).trans (by
      simpa only [r,sourceKPAdelicOrbitHeight_rational] using hx)
  obtain ⟨g,hg⟩ := ProjGenLinGroup.mk_surjective (sourceKPAdelicProjectiveProjection K hζ r)
  have hheight : sourceKPAdelicHeight K hζ g = sourceKPAdelicCoverHeight K hζ r := by
    unfold sourceKPAdelicCoverHeight
    rw [← hg,sourceKPAdelicHeightOnProjective_mk]
  have hband : Real.log (sourceKPAdelicHeight K hζ g) ∈ Set.Icc (Real.log c) (Real.log T) := by
    rw [hheight]
    exact ⟨Real.log_le_log hc hγ,
      Real.log_le_log (sourceKPAdelicCoverHeight_pos K hζ r) hupper⟩
  have hm := sourceKPHeightBand_cover_reduction K hζ v₀ (Real.log c) (Real.log T) r g hg.symm hband
  simpa only [r,sourceKPAutomorphicLevelMk_rational] using hm

theorem sourceKPAutomorphicOrbitHeight_uniform_pos :
    ∃ c : ℝ, 0 < c ∧ ∀ x : SourceKPAutomorphicLevel K hζ,
      c ≤ sourceKPAutomorphicOrbitHeight K hζ x := by
  obtain ⟨c,hc,h⟩ := sourceKPAdelicOrbitHeight_uniform_pos K hζ
  refine ⟨c,hc,fun x => ?_⟩
  obtain ⟨q,rfl⟩ := sourceKPAutomorphicLevelMk_surjective K hζ x
  exact h q

theorem sourceKPAutomorphicOrbitHeight_exhaustion_covers :
    (⋃ n : ℕ, {x : SourceKPAutomorphicLevel K hζ |
      sourceKPAutomorphicOrbitHeight K hζ x ≤ (n : ℝ)}) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨n,hn⟩ := exists_nat_gt (sourceKPAutomorphicOrbitHeight K hζ x)
  exact Set.mem_iUnion.mpr ⟨n,hn.le⟩

end
end ArtinMatthews
