module

public import ArtinMatthews.MarkedMemoryHistoryWeightTelescope


set_option backward.privateInPublic true
@[expose] public section

/-! The actual empty-memory boundary removes the remaining rho factors,
choice by choice and after any fixed restriction on genuine histories.
The weight and restriction still refer to the original indexed histories. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ) (hρ : ρ ≠ 0)
  (qStage : ℕ → ℝ) (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)

include hρ

/-- The literal boundary pairing term has no unmatched damping factor.
Its original signs, prime masses and slot probabilities are unchanged. -/
theorem markedMemoryChronologicalWeight_boundary (n j : ℕ) (z₀ : Z)
    {s : MarkedRawState P (pads+1) B Z} (history : MarkedMemoryChronologicalHistory hZ n s) :
    star (markedRawBoundary z₀ s) *
        markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history *
      markedRawBoundary z₀ (markedMemoryChronologicalTarget hZ history) =
    star (markedRawBoundary z₀ s) *
        markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q 1 qStage χ n j history *
      markedRawBoundary z₀ (markedMemoryChronologicalTarget hZ history) := by
  classical
  by_cases hs : s.2.2 = markedRawBoundaryEmptyMemory P B
  · by_cases ht : (markedMemoryChronologicalTarget hZ history).2.2 = markedRawBoundaryEmptyMemory P B
    · rw [markedMemoryChronologicalWeight_rho_empty ν V hZ ψ η d₀ Y Q ρ hρ qStage χ n j history hs ht]
    · simp [markedRawBoundary, ht]
  · simp [markedRawBoundary, hs]

/-- Any actual history restriction can be retained during cancellation;
in particular this does not replace global birth distinctness by a local
projection or change the underlying history multiplicities. -/
theorem markedMemoryChronologicalWeight_restricted_boundary_sum (n j : ℕ) (z₀ : Z)
    (keep : (s : MarkedRawState P (pads+1) B Z) → MarkedMemoryChronologicalHistory hZ n s → Prop) :
    (∑ s : MarkedRawState P (pads+1) B Z, (markedRawStateMass ν s : ℂ) *
      ∑ history : MarkedMemoryChronologicalHistory hZ n s,
        if keep s history then star (markedRawBoundary z₀ s) *
          markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history *
          markedRawBoundary z₀ (markedMemoryChronologicalTarget hZ history) else 0) =
    (∑ s : MarkedRawState P (pads+1) B Z, (markedRawStateMass ν s : ℂ) *
      ∑ history : MarkedMemoryChronologicalHistory hZ n s,
        if keep s history then star (markedRawBoundary z₀ s) *
          markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q 1 qStage χ n j history *
          markedRawBoundary z₀ (markedMemoryChronologicalTarget hZ history) else 0) := by
  classical
  congr 1
  funext s
  congr 1
  apply Finset.sum_congr rfl
  intro history _
  split_ifs
  · exact markedMemoryChronologicalWeight_boundary ν V hZ ψ η d₀ Y Q ρ hρ qStage χ n j z₀ history
  · rfl

/-- The unrestricted genuine operator composition has the same exact
boundary pairing. The proof uses its established finite choice expansion. -/
theorem markedMemoryChronologicalApply_boundary (n j : ℕ) (z₀ : Z) :
    (∑ s : MarkedRawState P (pads+1) B Z, (markedRawStateMass ν s : ℂ) *
      star (markedRawBoundary z₀ s) *
        markedMemoryChronologicalApply ν V hZ ψ η d₀ Y Q ρ qStage χ n j (markedRawBoundary z₀) s) =
    (∑ s : MarkedRawState P (pads+1) B Z, (markedRawStateMass ν s : ℂ) *
      star (markedRawBoundary z₀ s) *
        markedMemoryChronologicalApply ν V hZ ψ η d₀ Y Q 1 qStage χ n j (markedRawBoundary z₀) s) := by
  classical
  have h := markedMemoryChronologicalWeight_restricted_boundary_sum ν V hZ ψ η d₀ Y Q ρ hρ
    qStage χ n j z₀ (fun _ _ => True)
  simp only [ite_true] at h
  simp_rw [mul_assoc, ← Finset.mul_sum, markedMemoryChronological_sum] at h
  simpa only [mul_assoc] using h

end
end ArtinMatthews
