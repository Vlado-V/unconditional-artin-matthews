module

public import ArtinMatthews.MarkedMinorArcRawMemoryBulkIndices
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Exact finite integration over a genuine unordered batch of old indices.
The ordered deleted and surviving coordinates are obtained from the actual
old-index partition, never from a quotient of repeated particle values. -/
namespace ArtinMatthews
open scoped BigOperators

/-- Genuine finite product integration factors over any actual old deletion
subset, with every repeated value and every index multiplicity retained. -/
theorem markedRawMemory_subset_integral {X : Type*} [Fintype X] {k : ℕ}
    (S : Finset (Fin k)) (μ : X → ℂ)
    (f : (Fin S.card → X) → (Fin (Sᶜ).card → X) → ℂ) :
    (∑ a : Fin k → X, (∏ i, μ (a i))*
      f (markedRawSubsetTupleEquiv S a).1 (markedRawSubsetTupleEquiv S a).2)=
      ∑ deleted : Fin S.card → X, ∑ survivors : Fin (Sᶜ).card → X,
        (∏ i, μ (deleted i))*(∏ i, μ (survivors i))*f deleted survivors := by
  classical
  rw [← Equiv.sum_comp (markedRawSubsetTupleEquiv (X := X) S).symm]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro deleted _
  apply Finset.sum_congr rfl
  intro survivors _
  have he := (markedRawSubsetTupleEquiv (X := X) S).apply_symm_apply (deleted,survivors)
  rw [markedRawSubsetTupleEquiv_mass S μ,he]

/-- The true deleted/surviving index partition has exactly the original
number of old indexed particles. -/
theorem markedRawSubsetIndex_card {k : ℕ} (S : Finset (Fin k)) :
    S.card+(Sᶜ).card=k := by
  have hh := Fintype.card_congr (markedRawSubsetIndexEquiv S)
  simpa only [Fintype.card_sum,Fintype.card_fin] using hh

end ArtinMatthews
