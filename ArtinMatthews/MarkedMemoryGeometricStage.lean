module

public import ArtinMatthews.MarkedMemoryStageWeights
public import ArtinMatthews.MarkedMemoryHistoryPhaseFactor


set_option backward.privateInPublic true
@[expose] public section

/-! The original oriented geometric history is a particular stage-varying
history. The auxiliary rho factors telescope with the actual endpoint
memories, including every odd reflected-conjugate edge. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)

theorem markedMemoryStageWeight_rho
    (ψStage : ℕ → SchwartzMap ℝ ℂ) (ηStage : ℕ → ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (hρ : ρ≠0) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (n offset : ℕ) {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryStateRho hZ ρ s *
        markedMemoryStageWeight hZ ψStage ηStage d₀ Y Q χ ν V ρ qStage n offset H *
      markedMemoryStateRho hZ ρ (markedMemoryChronologicalTarget hZ H)=
        markedMemoryStageWeight hZ ψStage ηStage d₀ Y Q χ ν V 1 qStage n offset H := by
  induction n generalizing s offset with
  | zero => exact markedMemoryGhostChoiceWeight_rho ν V hZ (qStage offset) ρ hρ s H
  | succ n ih =>
    simp only [markedMemoryStageWeight,markedMemoryChronologicalTarget]
    rw [markedMemoryEdgeChoiceWeight_rho]
    calc
      _ = (markedMemoryStateRho hZ ρ s *
          markedMemoryGhostChoiceWeight ν V (qStage offset) ρ hZ s H.1 *
          markedMemoryStateRho hZ ρ (markedMemoryGhostChoiceTarget hZ s H.1)) *
        markedMemoryEdgeChoiceWeight ν V hZ (ψStage offset) (ηStage offset) d₀ Y Q 1 (χ offset)
          (markedMemoryGhostChoiceTarget hZ s H.1) H.2.1 *
        (markedMemoryStateRho hZ ρ (markedMemoryEdgeChoiceTarget hZ
            (markedMemoryGhostChoiceTarget hZ s H.1) H.2.1) *
          markedMemoryStageWeight hZ ψStage ηStage d₀ Y Q χ ν V ρ qStage n (offset+1) H.2.2 *
          markedMemoryStateRho hZ ρ (markedMemoryChronologicalTarget hZ H.2.2)) := by ring
      _ = _ := by rw [markedMemoryGhostChoiceWeight_rho ν V hZ (qStage offset) ρ hρ,ih]

theorem markedMemoryGeometricHistoryWeight_stage
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (n offset : ℕ) {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryGeometricHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ n offset H=
      markedMemoryStageWeight hZ
        (fun k => if orientation k then markedRawEdgeAdjointCutoff ψ else ψ)
        (fun k => if orientation k then fun u => star (η u) else η) d₀ Y Q
        (fun k => if orientation k then fun u => star (χ k u) else χ k)
        ν V ρ qStage n offset H := by
  induction n generalizing s offset with
  | zero => rfl
  | succ n ih =>
    simp only [markedMemoryGeometricHistoryWeight,markedMemoryStageWeight,ih]
    unfold markedMemoryGeometricEdgeChoiceWeight
    by_cases ho : orientation offset
    · simp only [ho,ite_true]
    · simp only [ho,Bool.false_eq_true,ite_false]

theorem markedMemoryGeometricHistoryWeight_rho_empty
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ) (hρ : ρ≠0)
    (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (n offset : ℕ) {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ n s)
    (hs : s.2.2=markedRawBoundaryEmptyMemory P B)
    (ht : (markedMemoryChronologicalTarget hZ H).2.2=markedRawBoundaryEmptyMemory P B) :
    markedMemoryGeometricHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ n offset H=
      markedMemoryGeometricHistoryWeight ν V hZ ψ η d₀ Y Q 1 orientation qStage χ n offset H := by
  rw [markedMemoryGeometricHistoryWeight_stage,markedMemoryGeometricHistoryWeight_stage]
  have hh := markedMemoryStageWeight_rho hZ ν V
    (fun k => if orientation k then markedRawEdgeAdjointCutoff ψ else ψ)
    (fun k => if orientation k then fun u => star (η u) else η) d₀ Y Q ρ hρ qStage
    (fun k => if orientation k then fun u => star (χ k u) else χ k) n offset H
  rwa [markedMemoryStateRho_empty hZ ρ s hs,
    markedMemoryStateRho_empty hZ ρ _ ht,one_mul,mul_one] at hh

end
end ArtinMatthews
