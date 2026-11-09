module

public import ArtinMatthews.MarkedMemoryHistoryLifespanScalarResidual
public import ArtinMatthews.MarkedMemoryTransitionAssembly


set_option backward.privateInPublic true
@[expose] public section

/-! Source-state transport leaves the literal chronological weight
and its ordered residual unchanged. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
  {s t : MarkedRawState P (pads+1) B Z} (hs : s=t) (H : MarkedMemoryChronologicalHistory hZ n s)

theorem markedMemoryChronologicalWeight_transport [DecidableEq J]
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (offset : ℕ) :
    markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n offset (markedMemoryHistoryTransport hZ hs H)=
      markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n offset H := by
  cases hs
  rfl

theorem markedMemoryHistoryEdgeResidual_transport [DecidableEq J]
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (offset : ℕ) :
    markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n offset (markedMemoryHistoryTransport hZ hs H)=
      markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n offset H := by
  cases hs
  rfl

end
end ArtinMatthews
