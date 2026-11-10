module

public import ArtinMatthews.MarkedRawStateInclude
public import ArtinMatthews.MarkedMemoryHistoryGhostChoice
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

/-! A position-window inclusion changes none of the actual ghost choices,
anchors, factorials or signed coefficients. -/

noncomputable section
namespace ArtinMatthews

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {M B : ℕ} {Z W : Finset (ℤ × ℤ)} (h : Z ⊆ W)
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (hW : ∀ z∈W,IsCoprime z.1 z.2)

def markedMemoryGhostChoiceInclude (s : MarkedRawState P M B Z)
    (c : MarkedMemoryGhostChoice hZ s) :
    MarkedMemoryGhostChoice hW (markedRawStateInclude h s) where
  deletion := c.deletion
  allowed := c.allowed
  sizes := c.sizes
  births := c.births

def markedMemoryGhostChoiceIncludeEquiv (s : MarkedRawState P M B Z) :
    MarkedMemoryGhostChoice hZ s ≃ MarkedMemoryGhostChoice hW (markedRawStateInclude h s) where
  toFun := markedMemoryGhostChoiceInclude h hZ hW s
  invFun c := ⟨c.deletion,c.allowed,c.sizes,c.births⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem markedMemoryGhostChoiceInclude_target (s : MarkedRawState P M B Z)
    (c : MarkedMemoryGhostChoice hZ s) :
    markedMemoryGhostChoiceTarget hW (markedRawStateInclude h s)
      (markedMemoryGhostChoiceInclude h hZ hW s c)=
      markedRawStateInclude h (markedMemoryGhostChoiceTarget hZ s c) := rfl

theorem markedMemoryGhostChoiceInclude_weight (ν : (j : J) → ↥(P j) → ℝ)
    (V : J → ℝ) (q ρ : ℝ) (s : MarkedRawState P M B Z)
    (c : MarkedMemoryGhostChoice hZ s) :
    markedMemoryGhostChoiceWeight ν V q ρ hW (markedRawStateInclude h s)
      (markedMemoryGhostChoiceInclude h hZ hW s c)=
      markedMemoryGhostChoiceWeight ν V q ρ hZ s c := rfl

end ArtinMatthews
