module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! The actual fixed compact cutoff supplies all finite row-bound constants. -/
noncomputable section
namespace ArtinMatthews

theorem markedBan_compact_cutoff_constants (ψ : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (ψ : ℝ → ℂ)) :
    ∃ A W : ℝ, 1 ≤ A ∧ 1 ≤ W ∧ (∀ u, ‖ψ u‖ ≤ W) ∧
      (∀ u, ψ u ≠ 0 → |u| ≤ A) := by
  obtain ⟨A,hA⟩ := hc.bddAbove_image continuous_norm.continuousOn
  obtain ⟨W,hW⟩ := (hc.isCompact_range ψ.continuous).bddAbove_image continuous_norm.continuousOn
  refine ⟨max 1 A,max 1 W,le_max_left _ _,le_max_left _ _,?_,?_⟩
  · intro u
    exact (hW (Set.mem_image_of_mem norm (Set.mem_range_self u))).trans (le_max_right _ _)
  · intro u hu
    have hh := (hA (Set.mem_image_of_mem norm (subset_tsupport ψ hu))).trans (le_max_right 1 A)
    simpa only [Real.norm_eq_abs] using hh

end ArtinMatthews
