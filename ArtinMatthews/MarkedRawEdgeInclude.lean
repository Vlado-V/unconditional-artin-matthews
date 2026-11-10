module

public import ArtinMatthews.MarkedRawStateInclude
public import ArtinMatthews.MarkedMinorArcRawEdgeAction
public import ArtinMatthews.MarkedMinorArcRawEdgeSymmetryCoefficients
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

/-! The actual raw edge embeds into a larger finite position space.
Its image consists exactly of choices whose target is in the smaller
window; all old indices, stores, fresh draws and both caps are literal. -/

noncomputable section
namespace ArtinMatthews

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z W : Finset (ℤ × ℤ)} (h : Z ⊆ W)
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (hW : ∀ z∈W,IsCoprime z.1 z.2)

def markedRawEdgeChoiceInclude (s : MarkedRawState P (pads+1) B Z)
    (c : MarkedRawEdgeChoice hZ s) :
    MarkedRawEdgeChoice hW (markedRawStateInclude h s) where
  target := ⟨c.target.1,h c.target.2⟩
  store := c.store
  promotions := c.promotions
  fresh := c.fresh
  promotion_hits := c.promotion_hits
  memory_bound := c.memory_bound

def markedRawEdgeChoiceWindowEquiv (s : MarkedRawState P (pads+1) B Z) :
    MarkedRawEdgeChoice hZ s ≃
      {c : MarkedRawEdgeChoice hW (markedRawStateInclude h s) // c.target.1∈Z} where
  toFun c := ⟨markedRawEdgeChoiceInclude h hZ hW s c,c.target.2⟩
  invFun c := ⟨⟨c.1.target.1,c.2⟩,c.1.store,c.1.promotions,c.1.fresh,
    c.1.promotion_hits,c.1.memory_bound⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem markedRawEdgeChoiceInclude_target (s : MarkedRawState P (pads+1) B Z)
    (c : MarkedRawEdgeChoice hZ s) :
    markedRawEdgeTargetState hW (markedRawStateInclude h s)
      (markedRawEdgeChoiceInclude h hZ hW s c)=
      markedRawStateInclude h (markedRawEdgeTargetState hZ s c) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem markedRawEdgeChoiceInclude_mass (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (s : MarkedRawState P (pads+1) B Z) (c : MarkedRawEdgeChoice hZ s) :
    markedRawEdgeChoicePrimeMass ν V hW (markedRawStateInclude h s)
      (markedRawEdgeChoiceInclude h hZ hW s c)=markedRawEdgeChoicePrimeMass ν V hZ s c := by
  simp only [markedRawEdgeChoicePrimeMass_eq_targetLast]
  rfl

theorem markedRawEdgeChoiceInclude_coefficient [DecidableEq J]
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B W → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (c : MarkedRawEdgeChoice hZ s) :
    markedRawEdgeChoiceCoefficient hW ψ η d₀ Y Q ρ χ (markedRawStateInclude h s)
      (markedRawEdgeChoiceInclude h hZ hW s c)=
      markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ (fun s => χ (markedRawStateInclude h s)) s c := rfl

end ArtinMatthews
