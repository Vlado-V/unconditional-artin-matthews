module

public import ArtinMatthews.MarkedMemoryHistoryWeightRho
public import ArtinMatthews.MarkedMemoryHistoryRhoCancellation
public import ArtinMatthews.MarkedRawBoundary


set_option backward.privateInPublic true
@[expose] public section

/-! Choice-by-choice telescoping of the actual chronological signed history.
Only the auxiliary rho damping is removed. All original choices, geometric
coefficients, slot probabilities, prime masses and birth factorials remain. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

omit [DecidableEq J] in
@[simp] theorem markedMemoryStateRho_one (s : MarkedRawState P (pads+1) B Z) :
    markedMemoryStateRho hZ 1 s = 1 := by simp [markedMemoryStateRho]

omit [DecidableEq J] in
/-- At rho=1 this is precisely the reduced signed coefficient, multiplied
by the original ordered birth mass and its factorial denominator. -/
theorem markedMemoryGhostChoiceWeight_one (qStage : ℝ)
    (s : MarkedRawState P (pads+1) B Z) (choice : MarkedMemoryGhostChoice hZ s) :
    markedMemoryGhostChoiceWeight ν V qStage 1 hZ s choice =
      ((markedMemoryGhostReducedCoefficient V qStage s.2.2 s.1.1 (hZ _ s.1.2)
          choice.deletion choice.sizes * markedRawGhostBirthMass ν choice.sizes choice.births : ℝ) : ℂ) := by
  simpa only [one_pow, Complex.ofReal_one, one_mul, mul_one] using
    markedMemoryGhostChoice_rho_cancellation ν V qStage 1 one_ne_zero hZ s choice

omit [DecidableEq J] in
theorem markedMemoryGhostChoiceWeight_rho (qStage ρ : ℝ) (hρ : ρ ≠ 0)
    (s : MarkedRawState P (pads+1) B Z) (choice : MarkedMemoryGhostChoice hZ s) :
    markedMemoryStateRho hZ ρ s * markedMemoryGhostChoiceWeight ν V qStage ρ hZ s choice *
        markedMemoryStateRho hZ ρ (markedMemoryGhostChoiceTarget hZ s choice) =
      markedMemoryGhostChoiceWeight ν V qStage 1 hZ s choice := by
  rw [markedMemoryGhostChoiceWeight_one]
  exact markedMemoryGhostChoice_rho_cancellation ν V qStage ρ hρ hZ s choice

/-- The exact whole-history cancellation, with the unmatched endpoint
factors shown explicitly for arbitrary initial and final memory. -/
theorem markedMemoryChronologicalWeight_rho
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ) (hρ : ρ ≠ 0)
    (qStage : ℕ → ℝ) (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (n j : ℕ) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryStateRho hZ ρ s *
        markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history *
      markedMemoryStateRho hZ ρ (markedMemoryChronologicalTarget hZ history) =
        markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q 1 qStage χ n j history := by
  induction n generalizing j s with
  | zero => exact markedMemoryGhostChoiceWeight_rho ν V hZ (qStage j) ρ hρ s history
  | succ n ih =>
    simp only [markedMemoryChronologicalWeight, markedMemoryChronologicalTarget]
    rw [markedMemoryEdgeChoiceWeight_rho]
    calc
      _ = (markedMemoryStateRho hZ ρ s *
          markedMemoryGhostChoiceWeight ν V (qStage j) ρ hZ s history.1 *
          markedMemoryStateRho hZ ρ (markedMemoryGhostChoiceTarget hZ s history.1)) *
        markedMemoryEdgeChoiceWeight ν V hZ ψ η d₀ Y Q 1 (χ j)
          (markedMemoryGhostChoiceTarget hZ s history.1) history.2.1 *
        (markedMemoryStateRho hZ ρ (markedMemoryEdgeChoiceTarget hZ
            (markedMemoryGhostChoiceTarget hZ s history.1) history.2.1) *
          markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n (j+1) history.2.2 *
          markedMemoryStateRho hZ ρ (markedMemoryChronologicalTarget hZ history.2.2)) := by ring
      _ = _ := by
        rw [markedMemoryGhostChoiceWeight_rho ν V hZ (qStage j) ρ hρ, ih]

omit [DecidableEq J] in
/-- Actual empty pending memory has no unmatched hit factor, including
at rho=0. -/
theorem markedMemoryStateRho_empty (ρ : ℝ) (s : MarkedRawState P (pads+1) B Z)
    (hs : s.2.2 = markedRawBoundaryEmptyMemory P B) :
    markedMemoryStateRho hZ ρ s = 1 := by
  unfold markedMemoryStateRho
  rw [hs]
  have hzero : markedRawPendingHits (markedRawBoundaryEmptyMemory P B)
      s.1.1 (hZ _ s.1.2) = 0 := by
    unfold markedRawPendingHits
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro k _
    exact Fin.elim0 k
  simp only [hzero, pow_zero, Complex.ofReal_one]

/-- The literal signed weight equals its rho=1 weight when both actual
endpoint memories are empty. No lifespan or primewise identity is assumed. -/
theorem markedMemoryChronologicalWeight_rho_empty
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ) (hρ : ρ ≠ 0)
    (qStage : ℕ → ℝ) (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (n j : ℕ) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s)
    (hs : s.2.2 = markedRawBoundaryEmptyMemory P B)
    (ht : (markedMemoryChronologicalTarget hZ history).2.2 = markedRawBoundaryEmptyMemory P B) :
    markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history =
      markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q 1 qStage χ n j history := by
  have h := markedMemoryChronologicalWeight_rho ν V hZ ψ η d₀ Y Q ρ hρ qStage χ n j history
  rwa [markedMemoryStateRho_empty hZ ρ s hs,
    markedMemoryStateRho_empty hZ ρ _ ht, one_mul, mul_one] at h

end
end ArtinMatthews
