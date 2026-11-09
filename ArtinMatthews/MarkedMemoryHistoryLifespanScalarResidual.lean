module

public import ArtinMatthews.MarkedMemoryHistoryLifespanScalar


set_option backward.privateInPublic true
@[expose] public section

/-! The original residual separates exactly into the scalar product of
actual ghost events, the original birth factorials, and the unchanged
edge residuals. The scalar product is then grouped by trace lifespan. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

theorem markedMemoryHistoryGhostScalarProduct_vertices {n : ℕ}
    {s : MarkedRawState P (pads+1) B Z} (history : MarkedMemoryChronologicalHistory hZ n s)
    (qStage : ℕ → ℝ) (j : ℕ) :
    markedMemoryHistoryGhostScalarProduct hZ history qStage j =
      ∏ v : Fin (n+1), markedMemoryGhostScalarProduct hZ (markedMemoryHistoryVertexState hZ history v)
        (markedMemoryHistoryVertexGhost hZ history v) (qStage (j+v.val)) := by
  unfold markedMemoryHistoryGhostScalarProduct
  rw [Fintype.prod_sigma]
  rfl

theorem markedMemoryHistoryGhostScalarProduct_zero (s : MarkedRawState P (pads+1) B Z)
    (ghost : MarkedMemoryChronologicalHistory hZ 0 s) (qStage : ℕ → ℝ) (j : ℕ) :
    markedMemoryHistoryGhostScalarProduct hZ (n := 0) ghost qStage j =
      markedMemoryGhostScalarProduct hZ s ghost (qStage j) := by
  rw [markedMemoryHistoryGhostScalarProduct_vertices, Fin.prod_univ_one]
  rfl

theorem markedMemoryHistoryGhostScalarProduct_succ {n : ℕ}
    {s : MarkedRawState P (pads+1) B Z} (history : MarkedMemoryChronologicalHistory hZ (n+1) s)
    (qStage : ℕ → ℝ) (j : ℕ) :
    markedMemoryHistoryGhostScalarProduct hZ history qStage j =
      markedMemoryGhostScalarProduct hZ s history.1 (qStage j) *
        markedMemoryHistoryGhostScalarProduct hZ history.2.2 qStage (j+1) := by
  rw [markedMemoryHistoryGhostScalarProduct_vertices, Fin.prod_univ_succ,
    markedMemoryHistoryGhostScalarProduct_vertices]
  apply congrArg₂ (fun x y : ℝ => x*y)
  · rfl
  · apply Finset.prod_congr rfl
    intro v _
    change markedMemoryGhostScalarProduct hZ (markedMemoryHistoryVertexState hZ history.2.2 v)
      (markedMemoryHistoryVertexGhost hZ history.2.2 v) (qStage (j+(v.val+1))) =
        markedMemoryGhostScalarProduct hZ (markedMemoryHistoryVertexState hZ history.2.2 v)
          (markedMemoryHistoryVertexGhost hZ history.2.2 v) (qStage ((j+1)+v.val))
    rw [show j+(v.val+1) = (j+1)+v.val by omega]

theorem markedMemoryHistoryBirthFactorials_zero (s : MarkedRawState P (pads+1) B Z)
    (ghost : MarkedMemoryChronologicalHistory hZ 0 s) :
    markedMemoryHistoryBirthFactorials hZ (n := 0) ghost = markedMemoryGhostBirthFactorial hZ s ghost := by
  unfold markedMemoryHistoryBirthFactorials
  rw [Fin.prod_univ_one]
  rfl

theorem markedMemoryHistoryBirthFactorials_succ {n : ℕ}
    {s : MarkedRawState P (pads+1) B Z} (history : MarkedMemoryChronologicalHistory hZ (n+1) s) :
    markedMemoryHistoryBirthFactorials hZ history = markedMemoryGhostBirthFactorial hZ s history.1 *
      markedMemoryHistoryBirthFactorials hZ history.2.2 := by
  unfold markedMemoryHistoryBirthFactorials
  rw [Fin.prod_univ_succ]
  rfl

variable [DecidableEq J]
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
  (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)

def markedMemoryHistoryEdgeResidualProduct :
    (n j : ℕ) → {s : MarkedRawState P (pads+1) B Z} →
      MarkedMemoryChronologicalHistory hZ n s → ℂ
  | 0,_,_,_ => 1
  | n+1,j,s,history =>
      markedMemoryEdgeResidual hZ ψ η d₀ Y Q (χ j)
        (markedMemoryGhostChoiceTarget hZ s history.1) history.2.1 *
      markedMemoryHistoryEdgeResidualProduct n (j+1) history.2.2

theorem markedMemoryHistoryResidual_ghostScalar (qStage : ℕ → ℝ)
    (n j : ℕ) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryHistoryResidual hZ ψ η d₀ Y Q qStage χ n j history =
      ((markedMemoryHistoryGhostScalarProduct hZ history qStage j /
        markedMemoryHistoryBirthFactorials hZ history : ℝ) : ℂ) *
      markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n j history := by
  induction n generalizing j s with
  | zero =>
    rw [markedMemoryHistoryGhostScalarProduct_zero, markedMemoryHistoryBirthFactorials_zero]
    change (markedMemoryGhostResidual hZ (qStage j) s history : ℂ) = _ * 1
    simpa only [mul_one] using congrArg (fun x : ℝ => (x : ℂ))
      (markedMemoryGhostResidual_scalar hZ s (show MarkedMemoryGhostChoice hZ s from history) (qStage j))
  | succ n ih =>
    change (markedMemoryGhostResidual hZ (qStage j) s history.1 : ℂ) *
      markedMemoryEdgeResidual hZ ψ η d₀ Y Q (χ j)
        (markedMemoryGhostChoiceTarget hZ s history.1) history.2.1 *
      markedMemoryHistoryResidual hZ ψ η d₀ Y Q qStage χ n (j+1) history.2.2 = _
    rw [ih, markedMemoryGhostResidual_scalar, markedMemoryHistoryGhostScalarProduct_succ,
      markedMemoryHistoryBirthFactorials_succ]
    change _ = _ * (markedMemoryEdgeResidual hZ ψ η d₀ Y Q (χ j)
      (markedMemoryGhostChoiceTarget hZ s history.1) history.2.1 *
      markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n (j+1) history.2.2)
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

theorem markedMemoryHistoryResidual_lifespanScalar (qStage : ℕ → ℝ)
    (n j : ℕ) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryHistoryResidual hZ ψ η d₀ Y Q qStage χ n j history =
      (((∏ a : MarkedMemoryHistoryTraceAddress hZ history,
        markedMemoryHistoryLifespanScalar hZ history qStage j a) /
        markedMemoryHistoryBirthFactorials hZ history : ℝ) : ℂ) *
      markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n j history := by
  rw [markedMemoryHistoryResidual_ghostScalar, markedMemoryHistoryGhostScalarProduct_lifespans]

end
end ArtinMatthews
