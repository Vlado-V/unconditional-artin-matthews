module

public import ArtinMatthews.MarkedMemoryHistoryArithmetic
public import ArtinMatthews.MarkedMemoryHistoryAnchorGates
public import ArtinMatthews.MarkedMemoryTransitionAssembly


set_option backward.privateInPublic true
@[expose] public section

/-! Literal chronological weights with a separate Schwartz kernel and
detector at each edge. The arithmetic factor is unchanged. In particular,
alternating adjoint cutoffs need no division by a fixed kernel. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (ψStage : ℕ → SchwartzMap ℝ ℂ) (ηStage : ℕ → ℝ → ℂ) (d₀ Y Q : ℝ)
  (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)

def markedMemoryStageResidualProduct :
    (n offset : ℕ) → {s : MarkedRawState P (pads+1) B Z} →
      MarkedMemoryChronologicalHistory hZ n s → ℂ
  | 0,_,_,_ => 1
  | n+1,k,s,H =>
      markedMemoryEdgeResidual hZ (ψStage k) (ηStage k) d₀ Y Q (χ k)
        (markedMemoryGhostChoiceTarget hZ s H.1) H.2.1 *
      markedMemoryStageResidualProduct n (k+1) H.2.2

def markedMemoryStageWeight (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (ρ : ℝ) (qStage : ℕ → ℝ) :
    (n offset : ℕ) → {s : MarkedRawState P (pads+1) B Z} →
      MarkedMemoryChronologicalHistory hZ n s → ℂ
  | 0,k,s,H => markedMemoryGhostChoiceWeight ν V (qStage k) ρ hZ s H
  | n+1,k,s,H =>
      markedMemoryGhostChoiceWeight ν V (qStage k) ρ hZ s H.1 *
      markedMemoryEdgeChoiceWeight ν V hZ (ψStage k) (ηStage k) d₀ Y Q ρ (χ k)
        (markedMemoryGhostChoiceTarget hZ s H.1) H.2.1 *
      markedMemoryStageWeight ν V ρ qStage n (k+1) H.2.2

theorem markedMemoryStageWeight_arithmetic
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (qStage : ℕ → ℝ)
    (n offset : ℕ) {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryStageWeight hZ ψStage ηStage d₀ Y Q χ ν V 1 qStage n offset H=
      (markedMemoryHistoryArithmeticWeight ν V hZ qStage offset H:ℂ)*
        markedMemoryStageResidualProduct hZ ψStage ηStage d₀ Y Q χ n offset H := by
  induction n generalizing s offset with
  | zero =>
    rw [markedMemoryStageWeight,markedMemoryStageResidualProduct,mul_one]
    exact (markedMemoryHistoryArithmeticWeight_zero ν V hZ qStage offset s H).symm
  | succ n ih =>
    rw [markedMemoryStageWeight,markedMemoryStageResidualProduct,ih,
      markedMemoryHistoryArithmeticWeight_succ]
    unfold markedMemoryEdgeChoiceWeight markedMemoryEdgeResidual
    ring

theorem markedMemoryStageWeight_anchor
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (ρ : ℝ) (qStage : ℕ → ℝ)
    (n offset : ℕ) {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ n s)
    (hw : markedMemoryStageWeight hZ ψStage ηStage d₀ Y Q χ ν V ρ qStage n offset H≠0) :
    MarkedMemoryHistoryAnchorAdmissible hZ H := by
  induction n generalizing s offset with
  | zero => trivial
  | succ n ih =>
    have hp := mul_ne_zero_iff.mp hw
    have he := (mul_ne_zero_iff.mp hp.1).2
    exact ⟨markedMemoryEdgeAnchorGate_of_weight_ne_zero ν V hZ (ψStage offset) (ηStage offset)
      d₀ Y Q ρ (χ offset) (markedMemoryGhostChoiceTarget hZ s H.1) H.2.1 he,
      ih (offset+1) H.2.2 hp.2⟩

theorem markedMemoryStageResidualProduct_constant
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (n offset : ℕ)
    {s : MarkedRawState P (pads+1) B Z} (H : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryStageResidualProduct hZ (fun _ => ψ) (fun _ => η) d₀ Y Q χ n offset H=
      markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n offset H := by
  induction n generalizing s offset with
  | zero => rfl
  | succ n ih =>
    change _ * markedMemoryStageResidualProduct hZ (fun _ => ψ) (fun _ => η) d₀ Y Q χ n (offset+1) H.2.2=
      _ * markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n (offset+1) H.2.2
    rw [ih]

theorem markedMemoryStageWeight_constant
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (ρ : ℝ) (qStage : ℕ → ℝ)
    (n offset : ℕ) {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryStageWeight hZ (fun _ => ψ) (fun _ => η) d₀ Y Q χ ν V ρ qStage n offset H=
      markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n offset H := by
  induction n generalizing s offset with
  | zero => rfl
  | succ n ih =>
    change _ * _ * markedMemoryStageWeight hZ (fun _ => ψ) (fun _ => η) d₀ Y Q χ ν V ρ qStage n (offset+1) H.2.2=
      _ * _ * markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n (offset+1) H.2.2
    rw [ih]

omit [DecidableEq J] in
theorem markedMemoryHistoryArithmeticWeight_transport
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (qStage : ℕ → ℝ) (offset : ℕ)
    {n : ℕ} {s t : MarkedRawState P (pads+1) B Z} (h : s=t)
    (H : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryHistoryArithmeticWeight ν V hZ qStage offset (markedMemoryHistoryTransport hZ h H)=
      markedMemoryHistoryArithmeticWeight ν V hZ qStage offset H := by
  cases h
  rfl

theorem markedMemoryStageResidualProduct_transport (n offset : ℕ)
    {s t : MarkedRawState P (pads+1) B Z} (h : s=t)
    (H : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryStageResidualProduct hZ ψStage ηStage d₀ Y Q χ n offset
      (markedMemoryHistoryTransport hZ h H)=
        markedMemoryStageResidualProduct hZ ψStage ηStage d₀ Y Q χ n offset H := by
  cases h
  rfl

end
end ArtinMatthews
