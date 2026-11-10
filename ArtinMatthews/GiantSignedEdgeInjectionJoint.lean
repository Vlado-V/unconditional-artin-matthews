module

public import ArtinMatthews.GiantSignedEdgeRetrieval
public import ArtinMatthews.MarkedMinorArcRawMemoryGroupedSubset
public import ArtinMatthews.GiantSignedEdgeOrderedJoint
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

/-! The factorial joint identity on the actual partial-injection carrier. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedMemory_injection_joint_factorial
    {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] {n a : J → ℕ}
    (μ : (j : J) → X j → ℂ)
    (H : ((j : J) → Fin (n j + a j) → X j) →
      ((j : J) → Fin (a j) → X j) → ((j : J) → Fin (n j) → X j) → ℂ)
    (hH : ∀ p u, MarkedRawGroupedTupleSymmetric (fun j => n j + a j)
      (fun old => H old p u)) :
    (∑ old : (j : J) → Fin (n j + a j) → X j,
      ((∏ j, ∏ i, μ j (old j i)) / (∏ j, (Nat.factorial (n j + a j) : ℂ))) *
        ∑ e : (j : J) → Fin (a j) ↪ Fin (n j + a j),
          H old (fun j => old j ∘ e j)
            (fun j => giantSignedRetrievalSurvivors (e j) (old j))) =
      ∑ p : (j : J) → Fin (a j) → X j,
        ∑ u : (j : J) → Fin (n j) → X j,
          ((∏ j, ∏ i, μ j (p j i)) * (∏ j, ∏ i, μ j (u j i))) /
            (∏ j, (Nat.factorial (n j) : ℂ)) *
            H (fun j => Fin.append (u j) (p j)) p u := by
  classical
  rw [← giantSignedMemory_ordered_joint_factorial μ H hH]
  apply Finset.sum_congr rfl
  intro old _
  congr 1
  rw [giantSignedPromotionFamily_sum]
  simp only [giantSignedPromotionEmbedding_retrieved, giantSignedPromotionEmbedding_survivors]

end
end ArtinMatthews
