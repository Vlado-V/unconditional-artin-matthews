module

public import ArtinMatthews.GiantSignedEdgeStorePromote
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

/-! Individual actual edge choices in the source row. Reindexing retains
the old-index injection, fresh target mass and both pending factors. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {B : Type*} [Fintype B] [DecidableEq B] {P : B → Finset ℕ}
    {t : B → ℕ}

def giantSignedEdgeMoveCoefficient (ν : (g : B) → P g → ℂ) (V : B → ℝ)
    (ρ : ℝ) (d : ℤ) (D : ℕ) (source target : GiantSignedPrimeTuple P t)
    (m : GiantSignedMemory P) (c : GiantSignedEdgeChoice t m.1) : ℂ :=
  giantSignedPromotionCharge V (fun g => (c.2.1 g).card) *
    giantSignedFreshPrimeMass ν c.2.1 target *
      if GiantSignedEdgeHits d m target c ∧ GiantSignedEdgePromotionBan D c.2.1 target then
        (giantSignedPendingDamping ρ m : ℂ) *
          (giantSignedPendingDamping ρ (giantSignedEdgeTarget d m source c) : ℂ)
      else 0

theorem giantSignedEdgeApply_eq_choice_sum (ν : (g : B) → P g → ℂ) (V : B → ℝ)
    (ρ : ℝ) (d : ℤ) (D : ℕ) (source : GiantSignedPrimeTuple P t)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℂ) (m : GiantSignedMemory P) :
    giantSignedEdgeApply ν V ρ d D source f m =
      ∑ c : GiantSignedEdgeChoice t m.1, ∑ target : GiantSignedPrimeTuple P t,
        giantSignedEdgeMoveCoefficient ν V ρ d D source target m c *
          f target (giantSignedEdgeTarget d m source c) := by
  unfold giantSignedEdgeApply GiantSignedEdgeChoice
  simp only [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.sum_congr rfl
  intro T _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro target _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : GiantSignedEdgeHits d m target ⟨S,T,e⟩ ∧
      GiantSignedEdgePromotionBan D T target
  · simp [giantSignedEdgeMoveCoefficient, h]
    ring
  · simp [giantSignedEdgeMoveCoefficient, h]

end
end ArtinMatthews
