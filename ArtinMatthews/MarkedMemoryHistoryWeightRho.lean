module

public import ArtinMatthews.MarkedMemoryHistoryEdgeChoice
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact damping factors in the actual edge choices, including the two
literal probability slot averages. The target count uses remaining target
memory, with stores and old-only promotions unchanged. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

/-- Literal pending-hit damping at a full raw state. -/
def markedMemoryStateRho (ρ : ℝ) (s : MarkedRawState P (pads+1) B Z) : ℂ :=
  ((ρ ^ markedRawPendingHits s.2.2 s.1.1 (hZ _ s.1.2) : ℝ) : ℂ)

omit [DecidableEq J] in
@[simp] theorem markedMemoryStateRho_slots (ρ : ℝ)
    (σ : MarkedMemorySlotPermutations J (pads+1)) (s : MarkedRawState P (pads+1) B Z) :
    markedMemoryStateRho hZ ρ (markedRawSlotEquiv σ s) = markedMemoryStateRho hZ ρ s := rfl

/-- Exact full coefficient factorization. All geometric tests, the full
cross ban, endpoint factors and Fourier integral remain in the middle. -/
theorem markedRawEdgeChoiceCoefficient_rho (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (choice : MarkedRawEdgeChoice hZ s) :
    markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s choice =
      markedMemoryStateRho hZ ρ s *
        markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q 1 χ s choice *
          markedMemoryStateRho hZ ρ (markedRawEdgeTargetState hZ s choice) := by
  classical
  unfold markedRawEdgeChoiceCoefficient markedMemoryStateRho
  dsimp only
  split_ifs <;> simp only [one_pow, Complex.ofReal_one, mul_zero, zero_mul]
  ring

/-- Both actual slot-card inverse factors and the prime integration mass
are retained when extracting the edge damping. -/
theorem markedMemoryEdgeChoiceWeight_rho
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (choice : MarkedMemoryEdgeChoice hZ s) :
    markedMemoryEdgeChoiceWeight ν V hZ ψ η d₀ Y Q ρ χ s choice =
      markedMemoryStateRho hZ ρ s *
        markedMemoryEdgeChoiceWeight ν V hZ ψ η d₀ Y Q 1 χ s choice *
          markedMemoryStateRho hZ ρ (markedMemoryEdgeChoiceTarget hZ s choice) := by
  unfold markedMemoryEdgeChoiceWeight
  rw [markedRawEdgeChoiceCoefficient_rho]
  change _ = markedMemoryStateRho hZ ρ s * _ *
    markedMemoryStateRho hZ ρ (markedRawEdgeTargetState hZ (markedRawSlotEquiv choice.1 s) choice.2.1)
  rw [markedMemoryStateRho_slots]
  ring

end
end ArtinMatthews
