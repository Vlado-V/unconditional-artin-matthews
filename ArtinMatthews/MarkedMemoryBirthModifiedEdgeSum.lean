module

public import ArtinMatthews.MarkedMinorArcRawEdgeModifierSymmetrized
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

/-! Exact finite choice expansion of both slot averages with a fresh-birth
modifier. The modifier is evaluated at the canonical target before the
literal final slot permutation. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators

def markedMemoryEdgeBirthModifiedWeight {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (i : J) → ↥(P i) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (φ : J → Option Nat.Primes → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (c : MarkedMemoryEdgeChoice hZ s) : ℂ :=
  markedMemoryEdgeChoiceWeight ν V hZ ψ η d₀ Y Q ρ χ s c *
    markedRawEdgeBirthModifier φ (markedRawSlotEquiv c.1 s) c.2.1

theorem markedMemoryEdgeBirthModifiedChoice_sum {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (i : J) → ↥(P i) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (φ : J → Option Nat.Primes → ℂ)
    (f : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) :
    (∑ c : MarkedMemoryEdgeChoice hZ s, markedMemoryEdgeBirthModifiedWeight ν V hZ ψ η d₀ Y Q ρ χ φ s c *
      f (markedMemoryEdgeChoiceTarget hZ s c)) =
      markedRawEdgeModifiedSymmetrized ν V hZ ψ η d₀ Y Q ρ χ (markedRawEdgeBirthModifier φ) f s := by
  classical
  unfold markedMemoryEdgeBirthModifiedWeight markedMemoryEdgeChoiceWeight markedMemoryEdgeChoiceTarget
  change (∑ c : Σ σ : MarkedMemorySlotPermutations J (pads+1),
      MarkedRawEdgeChoice hZ (markedRawSlotEquiv σ s) × MarkedMemorySlotPermutations J (pads+1),
    ((Fintype.card (MarkedMemorySlotPermutations J (pads+1)):ℂ)⁻¹)*
      (markedRawEdgeChoicePrimeMass ν V hZ (markedRawSlotEquiv c.1 s) c.2.1:ℂ)*
      markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ (markedRawSlotEquiv c.1 s) c.2.1*
      ((Fintype.card (MarkedMemorySlotPermutations J (pads+1)):ℂ)⁻¹)*
      markedRawEdgeBirthModifier φ (markedRawSlotEquiv c.1 s) c.2.1 *
      f (markedRawSlotEquiv c.2.2 (markedRawEdgeTargetState hZ (markedRawSlotEquiv c.1 s) c.2.1))) = _
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type]
  unfold markedRawEdgeModifiedSymmetrized markedRawSlotAverage markedRawEdgeModifiedApply
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro τ _
  ring

end ArtinMatthews
