module

public import ArtinMatthews.GiantSignedStateGhostGroup
public import ArtinMatthews.GiantSignedStateGhostLinear
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

/-! The source q/rho visit row has the same exact add/sub identities. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {M : ℕ}

theorem giantSignedStateGhostGroup_add
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ) (q ρ : ℝ)
    (w₁ w₂ : GiantSignedState PS PB M → ℂ)
    (C₁ u₁ C₂ u₂ : ℝ) (hC₁ : 0 ≤ C₁) (hu₁ : 0 < u₁) (hC₂ : 0 ≤ C₂) (hu₂ : 0 < u₂)
    (h₁ : ∀ s a m, ‖w₁ (s,a,m)‖ ≤ C₁ * u₁ ^ (∑ g, m.1 g))
    (h₂ : ∀ s a m, ‖w₂ (s,a,m)‖ ≤ C₂ * u₂ ^ (∑ g, m.1 g)) :
    giantSignedStateGhostGroup PS ν V q ρ (w₁+w₂) =
      giantSignedStateGhostGroup PS ν V q ρ w₁ + giantSignedStateGhostGroup PS ν V q ρ w₂ :=
  giantSignedStateGhostApply_add PS ν hν _ _ _ w₁ w₂ C₁ u₁ C₂ u₂ hC₁ hu₁ hC₂ hu₂ h₁ h₂

theorem giantSignedStateGhostGroup_sub
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ) (q ρ : ℝ)
    (w₁ w₂ : GiantSignedState PS PB M → ℂ)
    (C₁ u₁ C₂ u₂ : ℝ) (hC₁ : 0 ≤ C₁) (hu₁ : 0 < u₁) (hC₂ : 0 ≤ C₂) (hu₂ : 0 < u₂)
    (h₁ : ∀ s a m, ‖w₁ (s,a,m)‖ ≤ C₁ * u₁ ^ (∑ g, m.1 g))
    (h₂ : ∀ s a m, ‖w₂ (s,a,m)‖ ≤ C₂ * u₂ ^ (∑ g, m.1 g)) :
    giantSignedStateGhostGroup PS ν V q ρ (w₁-w₂) =
      giantSignedStateGhostGroup PS ν V q ρ w₁ - giantSignedStateGhostGroup PS ν V q ρ w₂ :=
  giantSignedStateGhostApply_sub PS ν hν _ _ _ w₁ w₂ C₁ u₁ C₂ u₂ hC₁ hu₁ hC₂ hu₂ h₁ h₂

end
end ArtinMatthews
