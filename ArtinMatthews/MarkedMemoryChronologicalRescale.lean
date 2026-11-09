module

public import ArtinMatthews.MarkedMemoryMeasureRescale


set_option backward.privateInPublic true
@[expose] public section

/-! Exact signed chronological change of atom normalization. Every
actual edge contributes its single inverse-V factor per band; ghost
weights, both slot factors, arbitrary cutoffs, and all signs stay exact. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (hV : ∀ j,V j≠0)
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
  (qStage : ℕ → ℝ) (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)

include hV

theorem markedMemoryChronologicalWeight_rescale (n k : ℕ)
    {s : MarkedRawState P (pads+1) B Z} (H : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n k H=
      (((∏ j,(V j)⁻¹:ℝ):ℂ)^n)*
        markedMemoryChronologicalWeight (markedMemoryScaledAtoms ν V) (fun _ => 1)
          hZ ψ η d₀ Y Q ρ qStage χ n k H := by
  induction n generalizing k s with
  | zero =>
    simpa only [markedMemoryChronologicalWeight,pow_zero,one_mul] using
      markedMemoryGhostChoiceWeight_rescale ν V (qStage k) ρ hZ s H
  | succ n ih =>
    change markedMemoryGhostChoiceWeight ν V (qStage k) ρ hZ s H.1*
      markedMemoryEdgeChoiceWeight ν V hZ ψ η d₀ Y Q ρ (χ k) _ H.2.1*
        markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n (k+1) H.2.2=_
    rw [markedMemoryGhostChoiceWeight_rescale,markedMemoryEdgeChoiceWeight_rescale ν V hV,
      ih (k+1) H.2.2]
    change _=(((∏ j,(V j)⁻¹:ℝ):ℂ)^(n+1))*
      (markedMemoryGhostChoiceWeight (markedMemoryScaledAtoms ν V) (fun _ => 1) (qStage k) ρ hZ s H.1*
      markedMemoryEdgeChoiceWeight (markedMemoryScaledAtoms ν V) (fun _ => 1) hZ ψ η d₀ Y Q ρ (χ k) _ H.2.1*
      markedMemoryChronologicalWeight (markedMemoryScaledAtoms ν V) (fun _ => 1)
        hZ ψ η d₀ Y Q ρ qStage χ n (k+1) H.2.2)
    rw [pow_succ]
    ring

theorem markedMemoryChronological_guarded_rescale (n k : ℕ)
    (s : MarkedRawState P (pads+1) B Z)
    (keep : MarkedMemoryChronologicalHistory hZ n s → Prop)
    (f : MarkedRawState P (pads+1) B Z → ℂ) :
    (∑ H : MarkedMemoryChronologicalHistory hZ n s,
      if keep H then markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n k H*
        f (markedMemoryChronologicalTarget hZ H) else 0)=
      (((∏ j,(V j)⁻¹:ℝ):ℂ)^n)*
        (∑ H : MarkedMemoryChronologicalHistory hZ n s,
          if keep H then markedMemoryChronologicalWeight (markedMemoryScaledAtoms ν V) (fun _ => 1)
            hZ ψ η d₀ Y Q ρ qStage χ n k H*f (markedMemoryChronologicalTarget hZ H) else 0) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H _
  by_cases hh : keep H
  · simp only [ite_eq_left hh,markedMemoryChronologicalWeight_rescale ν V hV hZ ψ η d₀ Y Q ρ qStage χ n k H]
    ring
  · simp only [ite_eq_right hh,mul_zero]

end
end ArtinMatthews
