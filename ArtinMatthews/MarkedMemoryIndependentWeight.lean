module

public import ArtinMatthews.MarkedMemoryIndependentSourceScalar
public import ArtinMatthews.MarkedMemoryIndependentBirthFactorials
public import ArtinMatthews.MarkedMemoryIndependentBirthWeight
public import ArtinMatthews.MarkedMemoryIndependentRunCount
public import ArtinMatthews.MarkedMemoryIndependentRunFiber
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

/-! Elementwise exact weights on independent lifespan data. No quotient
or orbit multiplicity is used. Both slot normalizations, arbitrary
ordered-state multipliers and geometric tests remain in the literal
edge residual product; the original target test is retained verbatim. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  {A : J → Type*} [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)]
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (order : Fin n → J → Equiv.Perm (Fin pads))

local notation "history" => markedMemoryIndependentHistory hZ d order
local notation "addr" => markedMemoryIndependentAddressEquiv hZ d order

variable (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
  (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)

theorem markedMemoryIndependent_residual (qStage : ℕ → ℝ) (offset : ℕ) :
    markedMemoryHistoryResidual hZ ψ η d₀ Y Q qStage χ n offset history =
      (((∏ a : Σ j, A j, markedMemoryIndependentLifespanScalar hZ d qStage offset a) /
        markedMemoryIndependentBirthFactorials hZ d : ℝ) : ℂ) *
      markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n offset history := by
  have hs : (∏ a : MarkedMemoryHistoryTraceAddress hZ history,
      markedMemoryHistoryLifespanScalar hZ history qStage offset a) =
        ∏ a : Σ j, A j, markedMemoryIndependentLifespanScalar hZ d qStage offset a := by
    rw [← Equiv.prod_comp (addr).symm]
    exact Finset.prod_congr rfl (fun a _ => markedMemoryIndependent_lifespanScalar hZ d order qStage offset a)
  rw [markedMemoryHistoryResidual_lifespanScalar, hs, markedMemoryIndependent_birthFactorials]

theorem markedMemoryIndependent_source_residual (q : ℝ) :
    markedMemoryHistoryResidual hZ ψ η d₀ Y Q (markedMemoryHistoryVisitSchedule q n) χ n 0 history =
      (((∏ a : Σ j, A j, markedMemoryIndependentLifespanSourceScalar hZ d q a) /
        markedMemoryIndependentBirthFactorials hZ d : ℝ) : ℂ) *
      markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n 0 history := by
  rw [markedMemoryIndependent_residual]
  simp_rw [markedMemoryIndependentLifespanScalar_source]

theorem markedMemoryIndependent_weight
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (qStage : ℕ → ℝ) (offset : ℕ) :
    markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q 1 qStage χ n offset history =
      ((∏ a : Σ j, A j, markedMemoryIndependentBirthMass hZ d ν V a *
        (V a.1)⁻¹ ^ markedMemoryIndependentRunCount hZ d a : ℝ) : ℂ) *
      (((∏ a : Σ j, A j, markedMemoryIndependentLifespanScalar hZ d qStage offset a) /
        markedMemoryIndependentBirthFactorials hZ d : ℝ) : ℂ) *
      markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n offset history := by
  rw [markedMemoryIndependent_runWeight, markedMemoryIndependent_residual]
  ring

theorem markedMemoryIndependent_source_weight
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (q : ℝ) :
    markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q 1
        (markedMemoryHistoryVisitSchedule q n) χ n 0 history =
      ((∏ a : Σ j, A j, markedMemoryIndependentBirthMass hZ d ν V a *
        (V a.1)⁻¹ ^ markedMemoryIndependentRunCount hZ d a : ℝ) : ℂ) *
      (((∏ a : Σ j, A j, markedMemoryIndependentLifespanSourceScalar hZ d q a) /
        markedMemoryIndependentBirthFactorials hZ d : ℝ) : ℂ) *
      markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n 0 history := by
  rw [markedMemoryIndependent_runWeight, markedMemoryIndependent_source_residual]
  ring

/-- The complete per-identity scalar and prime contribution, while the
literal edge product and factorial denominator are retained. -/
theorem markedMemoryIndependent_source_lifespan_weight
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (q : ℝ) :
    markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q 1
        (markedMemoryHistoryVisitSchedule q n) χ n 0 history =
      (((∏ a : Σ j, A j,
          markedMemoryIndependentBirthMass hZ d ν V a *
          (V a.1)⁻¹ ^ markedMemoryIndependentRunCount hZ d a *
          markedMemoryIndependentLifespanSourceScalar hZ d q a) /
        markedMemoryIndependentBirthFactorials hZ d : ℝ) : ℂ) *
      markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n 0 history := by
  rw [markedMemoryIndependent_source_weight, Finset.prod_mul_distrib]
  push_cast
  simp only [Finset.prod_mul_distrib]
  ring

theorem markedMemoryIndependent_source_weight_integrand
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (q : ℝ)
    (targetTest : MarkedRawState P (pads+1) B Z → ℂ) :
    markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q 1
        (markedMemoryHistoryVisitSchedule q n) χ n 0 history *
      targetTest (markedMemoryChronologicalTarget hZ history) =
      ((∏ a : Σ j, A j, markedMemoryIndependentBirthMass hZ d ν V a *
        (V a.1)⁻¹ ^ markedMemoryIndependentRunCount hZ d a : ℝ) : ℂ) *
      (((∏ a : Σ j, A j, markedMemoryIndependentLifespanSourceScalar hZ d q a) /
        markedMemoryIndependentBirthFactorials hZ d : ℝ) : ℂ) *
      markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n 0 history *
      targetTest (markedMemoryChronologicalTarget hZ history) := by
  rw [markedMemoryIndependent_source_weight]

end
end ArtinMatthews
