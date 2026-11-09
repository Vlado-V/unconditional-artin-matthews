module

public import ArtinMatthews.MarkedMemoryGoodBoundary


set_option backward.privateInPublic true
@[expose] public section

/-! The first-bad identities instantiated with the literal first and
full-trial second good tests at every actual chronological edge. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedMemoryChronologicalWeight_actual_good
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (x : ℝ)
    (ν : (j : J) → ↥(markedRawActualPrimeBand e x j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (r d₀ Y Q ρ : ℝ) (w : Z → ℤ × ℤ)
    (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ)
    (n j : ℕ) {s : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z}
    (h : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage
      (fun i => markedRawDirtyGoodCutoff e x r d₀ Y w (χ i)) n j h =
      if MarkedMemoryHistoryGood hZ (fun _ => MarkedRawDirtyGood e x r d₀ Y w) n j h then
        markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j h else 0 := by
  have hχ : (fun i => markedRawDirtyGoodCutoff e x r d₀ Y w (χ i)) =
      (fun i u => if MarkedRawDirtyGood e x r d₀ Y w u then χ i u else 0) := by
    funext i u
    exact markedRawDirtyGoodCutoff_eq_ite e x r d₀ Y w (χ i) u
  rw [hχ]
  exact markedMemoryChronologicalWeight_good_cutoff ν V hZ ψ η d₀ Y Q ρ qStage χ
    (fun _ => MarkedRawDirtyGood e x r d₀ Y w) n j h

theorem markedMemoryBoundaryPairing_actual_good_first_bad
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (x : ℝ)
    (ν : (j : J) → ↥(markedRawActualPrimeBand e x j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (r d₀ Y Q ρ : ℝ) (w : Z → ℤ × ℤ)
    (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ)
    (n j : ℕ) (z₀ : Z) :
    markedMemoryBoundaryPairing ν V hZ ψ η d₀ Y Q ρ qStage χ n j z₀ -
      markedMemoryBoundaryPairing ν V hZ ψ η d₀ Y Q ρ qStage
        (fun i => markedRawDirtyGoodCutoff e x r d₀ Y w (χ i)) n j z₀ =
      ∑ s,(markedRawStateMass ν s:ℂ)*star (markedRawBoundary z₀ s)*
        markedMemoryFirstBadApply ν V hZ ψ η d₀ Y Q ρ qStage χ
          (fun _ => MarkedRawDirtyGood e x r d₀ Y w) n j (markedRawBoundary z₀) s := by
  have hχ : (fun i => markedRawDirtyGoodCutoff e x r d₀ Y w (χ i)) =
      (fun i u => if MarkedRawDirtyGood e x r d₀ Y w u then χ i u else 0) := by
    funext i u
    exact markedRawDirtyGoodCutoff_eq_ite e x r d₀ Y w (χ i) u
  rw [hχ]
  exact markedMemoryBoundaryPairing_first_bad ν V hZ ψ η d₀ Y Q ρ qStage χ
    (fun _ => MarkedRawDirtyGood e x r d₀ Y w) n j z₀

end
end ArtinMatthews
