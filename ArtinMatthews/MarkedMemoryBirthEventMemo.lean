module

public import ArtinMatthews.MarkedMemoryBirthEventPositive
public import ArtinMatthews.MarkedMemoryHistoryPivotCompatible


set_option backward.privateInPublic true
@[expose] public section

/-! The original permutation-event boundary is dominated by the
positive conditional word. Actual chronological memo theorems discharge
every gate and compatibility premise in the finite comparison. -/

noncomputable section
namespace ArtinMatthews

set_option backward.isDefEq.respectTransparency false in
theorem markedMemoryBirthEventBoundary_le_positive_actual
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (i : J) → ↥(P i) → ℝ) (hν : ∀ i p,0 ≤ ν i p) (V : J → ℝ)
    {pads B N : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N)) (z₀ : Z) :
    ‖markedMemoryBirthEventBoundaryPairing ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ z₀‖ ≤
      markedMemoryPositivePivotBoundary ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ z₀ := by
  apply markedMemoryBirthEventBoundary_le_positive ν hν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ z₀
  · intro s h he
    exact markedMemoryHistory_initial_stageGate hZ h σ he
  · intro s h he
    rw [markedMemoryHistory_initialPivotValues hZ h]
    exact markedMemoryHistory_pivotCompatible hZ h σ he

end ArtinMatthews
