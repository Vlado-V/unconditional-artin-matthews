module

public import Mathlib.Analysis.Complex.Norm
public import ArtinMatthews.MarkedPhysicalCanonicalWeightSum
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

/-! A finite nonnegative target-extension inequality, factored separately
so physical coefficient definitions need not unfold in finite algebra. -/
noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysical_finite_block_le {ι κ : Type*} [Fintype ι]
    (s : ι → Finset κ) (t : Finset κ) (F : ι → κ → ℂ) (w : ι → κ → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ i z, z ∈ s i → ‖F i z‖ ≤ C*(if z ∈ t then w i z else 0))
    (hw : ∀ i z, z ∈ t → 0 ≤ w i z) :
    (∑ i, ∑ z ∈ s i, ‖F i z‖) ≤ C * ∑ i, ∑ z ∈ t, w i z := by
  calc
    _ ≤ ∑ i, ∑ z ∈ s i, C*(if z ∈ t then w i z else 0) := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum (fun z hz => hF i z hz)
    _ = C * ∑ i, ∑ z ∈ s i, if z ∈ t then w i z else 0 := by simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact Finset.sum_le_sum (fun i _ => markedPhysical_sum_indicator_le (s i) t (w i) (hw i))

end ArtinMatthews
