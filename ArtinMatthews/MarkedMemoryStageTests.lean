module

public import ArtinMatthews.MarkedMemoryGeometricStage
public import ArtinMatthews.MarkedMemoryCopiedSlotGeometry


set_option backward.privateInPublic true
@[expose] public section

/-! Arbitrary ordered endpoint tests factor without changing their
arguments. The target test is evaluated before the final target slot
permutation, exactly as in the original raw coefficient. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)

def markedMemoryStageTestProduct (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) :
    (n offset : ℕ) → {s : MarkedRawState P (pads+1) B Z} →
      MarkedMemoryChronologicalHistory hZ n s → ℂ
  | 0,_,_,_ => 1
  | n+1,k,s,H =>
      χ k (markedRawSlotEquiv H.2.1.1 (markedMemoryGhostChoiceTarget hZ s H.1)) *
      χ k (markedRawEdgeTargetState hZ
        (markedRawSlotEquiv H.2.1.1 (markedMemoryGhostChoiceTarget hZ s H.1)) H.2.1.2.1) *
      markedMemoryStageTestProduct χ n (k+1) H.2.2

theorem markedMemoryEdgeChoiceWeight_test_factor
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (c : MarkedMemoryEdgeChoice hZ s) :
    markedMemoryEdgeChoiceWeight ν V hZ ψ η d₀ Y Q ρ χ s c=
      markedMemoryEdgeChoiceWeight ν V hZ ψ η d₀ Y Q ρ (fun _ => 1) s c *
        χ (markedRawSlotEquiv c.1 s) *
        χ (markedRawEdgeTargetState hZ (markedRawSlotEquiv c.1 s) c.2.1) := by
  unfold markedMemoryEdgeChoiceWeight
  simp_rw [markedRawEdgeChoiceCoefficient_eq_joint]
  rw [markedRawEdgeJointCoefficient_test_factor hZ ψ η d₀ Y Q ρ χ]
  ring

theorem markedMemoryStageWeight_test_factor
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (ψStage : ℕ → SchwartzMap ℝ ℂ) (ηStage : ℕ → ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (qStage : ℕ → ℝ) (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (n offset : ℕ) {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryStageWeight hZ ψStage ηStage d₀ Y Q χ ν V ρ qStage n offset H=
      markedMemoryStageWeight hZ ψStage ηStage d₀ Y Q (fun _ _ => 1) ν V ρ qStage n offset H *
        markedMemoryStageTestProduct hZ χ n offset H := by
  induction n generalizing s offset with
  | zero => simp only [markedMemoryStageWeight,markedMemoryStageTestProduct,mul_one]
  | succ n ih =>
    rw [markedMemoryStageWeight,markedMemoryStageWeight,markedMemoryStageTestProduct,
      markedMemoryEdgeChoiceWeight_test_factor,ih]
    ring

theorem markedMemoryGeometricHistoryWeight_test_factor
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (n offset : ℕ) {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryGeometricHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ n offset H=
      markedMemoryGeometricHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage (fun _ _ => 1) n offset H *
        markedMemoryStageTestProduct hZ (fun k => if orientation k then fun u => star (χ k u) else χ k)
          n offset H := by
  rw [markedMemoryGeometricHistoryWeight_stage,markedMemoryGeometricHistoryWeight_stage]
  have hχ : (fun k => if orientation k then fun _ : MarkedRawState P (pads+1) B Z => star (1:ℂ)
      else fun _ => (1:ℂ))=(fun _ _ => 1) := by
    funext k u
    simp only [star_one,ite_self]
  rw [hχ,markedMemoryStageWeight_test_factor]

end
end ArtinMatthews
