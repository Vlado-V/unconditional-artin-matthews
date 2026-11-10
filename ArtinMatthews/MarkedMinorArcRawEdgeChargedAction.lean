module

public import ArtinMatthews.MarkedMinorArcRawEdgeJointCoefficient
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Independent storage and promotion charges on the original literal
edge choices.  The physical edge is recovered exactly by promotion charge
V^-1 and storage charge one; its transpose exchanges these charges. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

def markedRawEdgeChoiceCharge {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (c : MarkedRawEdgeChoice hZ s) : ℂ :=
  ∏ j, δ j ^ (if (c.promotions j).isSome then 1 else 0) *
    γ j ^ (if c.store j then 1 else 0)

/-- Promoted coordinates introduce no fresh-prime measure factor. -/
def markedRawEdgeChoiceFreshMass {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (c : MarkedRawEdgeChoice hZ s) : ℂ :=
  (markedRawEdgeChoicePrimeMass ν (fun _ => 1) hZ s c : ℂ)

/-- The exact original finite state update, with its two charges exposed
and an arbitrary joint endpoint coefficient. -/
def markedRawEdgeChargedApply {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (K : MarkedRawState P (pads+1) B Z → MarkedRawState P (pads+1) B Z → ℂ)
    (f : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) : ℂ :=
  ∑ c : MarkedRawEdgeChoice hZ s,
    markedRawEdgeChoiceCharge δ γ hZ s c * markedRawEdgeChoiceFreshMass ν hZ s c *
      K s (markedRawEdgeTargetState hZ s c) * f (markedRawEdgeTargetState hZ s c)

/-- The original promotion factor is recovered even when a V or an atom
vanishes. No reciprocal cancellation is used to identify the literal row. -/
theorem markedRawEdgeChoiceCharge_original
    {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (c : MarkedRawEdgeChoice hZ s) :
    markedRawEdgeChoiceCharge (fun j => ((V j)⁻¹ : ℝ)) (fun _ => 1) hZ s c *
      markedRawEdgeChoiceFreshMass ν hZ s c = (markedRawEdgeChoicePrimeMass ν V hZ s c : ℂ) := by
  unfold markedRawEdgeChoiceCharge markedRawEdgeChoiceFreshMass
  simp only [markedRawEdgeChoicePrimeMass_eq_targetLast, Complex.ofReal_prod]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hp : (c.promotions j).isSome <;> simp [hp]

/-- The actual physical full row is exactly this charged action with the
proved joint coefficient, not an abstract replacement operator. -/
theorem markedRawEdgeApply_eq_charged
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ f : MarkedRawState P (pads+1) B Z → ℂ) :
    markedRawEdgeApply ν V hZ ψ η d₀ Y Q ρ χ f =
      markedRawEdgeChargedApply ν (fun j => ((V j)⁻¹ : ℝ)) (fun _ => 1) hZ
        (markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ) f := by
  funext s
  unfold markedRawEdgeApply markedRawEdgeChargedApply
  apply Finset.sum_congr rfl
  intro c _
  rw [markedRawEdgeChoiceCharge_original, markedRawEdgeChoiceCoefficient_eq_joint]

end
end ArtinMatthews
