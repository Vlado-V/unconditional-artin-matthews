module

public import ArtinMatthews.MarkedMinorArcRawEdgeAbsoluteTranspose
public import ArtinMatthews.MarkedMinorArcRawEdgeChoiceCauchy
public import ArtinMatthews.MarkedMinorArcRawGhostEnergyReduction
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

/-! Evaluation of the actual Cauchy reverse energy by the proved full
store/promote transpose, retaining the original factorial state measure. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

theorem markedRawEdgeChoiceReverseEnergy_eq_absApply
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ v₀ : ℝ) (χ f : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) :
    (markedRawEdgeChoiceReverseEnergy ν V hZ ψ η d₀ Y Q ρ v₀ χ f s : ℂ) =
      (markedRawMemorySchurWeight v₀ s.2.2 : ℂ) *
        markedRawEdgeAbsApply ν V hZ ψ η d₀ Y Q ρ χ
          (fun t => ((‖f t‖^2 / markedRawMemorySchurWeight v₀ t.2.2 : ℝ) : ℂ)) s := by
  unfold markedRawEdgeChoiceReverseEnergy markedRawEdgeAbsApply
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  dsimp only [markedRawEdgeTargetState]
  ring

/-- The full integrated reverse energy is exactly the concrete reversed
charged action. This follows from the original indexed choice transpose,
with no column or adjoint estimate among the assumptions. -/
theorem markedRawEdgeChoiceReverseEnergy_sum_eq_reversed_action
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ v₀ : ℝ) (χ f : MarkedRawState P (pads+1) B Z → ℂ)
    (hχ : ∀ z active, MarkedRawMemorySymmetric (fun m => χ (z,(active,m))))
    (hf : ∀ z active, MarkedRawMemorySymmetric (fun m => f (z,(active,m)))) :
    ((∑ s, markedRawStateMass ν s *
      markedRawEdgeChoiceReverseEnergy ν V hZ ψ η d₀ Y Q ρ v₀ χ f s : ℝ) : ℂ) =
      ∑ s, (markedRawStateMass ν s : ℂ) *
        ((‖f s‖^2 / markedRawMemorySchurWeight v₀ s.2.2 : ℝ) : ℂ) *
        markedRawEdgeChargedApply ν (fun _ => 1) (fun j => ((V j)⁻¹ : ℝ)) hZ
          (fun target source => (‖markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ source target‖ : ℂ))
          (fun t => (markedRawMemorySchurWeight v₀ t.2.2 : ℂ)) s := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  have ht := markedRawEdgeAbsApply_transpose ν V hZ ψ η d₀ Y Q ρ χ
    (fun t => ((‖f t‖^2 / markedRawMemorySchurWeight v₀ t.2.2 : ℝ) : ℂ))
    (fun t => (markedRawMemorySchurWeight v₀ t.2.2 : ℂ)) hχ
    (markedRawGhostEnergyReweight_symmetric v₀ f hf)
    (fun _ _ => markedRawMemorySchurWeight_symmetric v₀)
  rw [← ht]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul,
    markedRawEdgeChoiceReverseEnergy_eq_absApply, mul_assoc]

end
end ArtinMatthews
