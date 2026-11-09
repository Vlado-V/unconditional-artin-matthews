module

public import ArtinMatthews.MarkedMemoryIndependentRunFiber
public import ArtinMatthews.MarkedMemoryIndependentSourceScalar
public import ArtinMatthews.MarkedMemoryIndependentBirthFactorials


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
