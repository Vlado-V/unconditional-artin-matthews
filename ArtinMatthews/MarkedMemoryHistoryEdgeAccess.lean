module

public import ArtinMatthews.MarkedMemoryHistoryLifespanScalar
public import ArtinMatthews.MarkedMemoryHistoryLifespanScalarEvents
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Literal finite edge accessors and their actual chronological trace
positions. No local choice is reconstructed or replaced in this module. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

def markedMemoryHistoryVertexEdge :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      (history : MarkedMemoryChronologicalHistory hZ n s) → (v : Fin n) →
        MarkedMemoryEdgeChoice hZ (markedMemoryGhostChoiceTarget hZ
          (markedMemoryHistoryVertexState hZ history v.castSucc)
          (markedMemoryHistoryVertexGhost hZ history v.castSucc))
  | 0, _, _, v => Fin.elim0 v
  | _+1, _, history, v => Fin.cases history.2.1
      (fun w => markedMemoryHistoryVertexEdge history.2.2 w) v

theorem markedMemoryHistoryVertexState_zero {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryHistoryVertexState hZ history 0 = s := by
  cases n <;> rfl

theorem markedMemoryHistoryVertexEdge_target {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (v : Fin n) :
    markedMemoryEdgeChoiceTarget hZ _ (markedMemoryHistoryVertexEdge hZ history v) =
      markedMemoryHistoryVertexState hZ history v.succ := by
  induction n generalizing s with
  | zero => exact Fin.elim0 v
  | succ n ih =>
    refine Fin.cases ?_ (fun w => ?_) v
    · change markedMemoryEdgeChoiceTarget hZ _ history.2.1 = markedMemoryHistoryVertexState hZ history.2.2 0
      exact (markedMemoryHistoryVertexState_zero hZ history.2.2).symm
    · exact ih history.2.2 w

theorem markedMemoryHistoryVertexState_trace {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (v : Fin (n+1)) :
    markedMemoryHistoryTraceState hZ history (2*v.val) = markedMemoryHistoryVertexState hZ history v :=
  (congrArg (markedMemoryHistoryTraceState hZ history) (markedMemoryHistoryGhostTime_eq n v)).symm.trans
    (markedMemoryHistoryTraceState_stage hZ history (markedMemoryHistoryVertexStage n v))

theorem markedMemoryHistoryEdgeSource_trace {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (v : Fin n) :
    markedMemoryHistoryTraceState hZ history (2*v.val+1) =
      markedMemoryGhostChoiceTarget hZ (markedMemoryHistoryVertexState hZ history v.castSucc)
        (markedMemoryHistoryVertexGhost hZ history v.castSucc) := by
  have ht : markedMemoryHistoryGhostTime n v.castSucc+1 = 2*v.val+1 := by
    rw [markedMemoryHistoryGhostTime_eq]
    rfl
  exact (congrArg (markedMemoryHistoryTraceState hZ history) ht).symm.trans
    (markedMemoryHistoryGhostTarget_trace hZ history v.castSucc)

theorem markedMemoryHistoryEdgeTarget_trace {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (v : Fin n) :
    markedMemoryHistoryTraceState hZ history (2*(v.val+1)) =
      markedMemoryEdgeChoiceTarget hZ _ (markedMemoryHistoryVertexEdge hZ history v) :=
  (markedMemoryHistoryVertexState_trace hZ history v.succ).trans
    (markedMemoryHistoryVertexEdge_target hZ history v).symm

theorem markedMemoryHistoryVertexEdge_birthType {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (v : Fin n) :
    MarkedMemoryHistoryTraceBirth hZ history (2*v.val+1) =
      MarkedMemoryEdgeBirthIndex (markedMemoryHistoryVertexEdge hZ history v) := by
  induction n generalizing s with
  | zero => exact Fin.elim0 v
  | succ n ih =>
    refine Fin.cases ?_ (fun w => ?_) v
    · rfl
    · have hw : (w.succ : ℕ) = w.val+1 := rfl
      have ht : 2*(w.succ.val)+1 = (2*w.val+1)+2 := by omega
      rw [ht]
      exact ih history.2.2 w

theorem markedMemoryHistoryVertexEdge_step {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (v : Fin n) :
    HEq (markedMemoryHistoryTraceStep hZ history (2*v.val+1))
      (markedMemoryEdgeSlotPopulationOrigin hZ _ (markedMemoryHistoryVertexEdge hZ history v)) := by
  induction n generalizing s with
  | zero => exact Fin.elim0 v
  | succ n ih =>
    refine Fin.cases ?_ (fun w => ?_) v
    · rfl
    · have hw : (w.succ : ℕ) = w.val+1 := rfl
      have ht : 2*(w.succ.val)+1 = (2*w.val+1)+2 := by omega
      rw [ht]
      exact ih history.2.2 w

theorem markedMemoryHistoryVertexGhost_birthType {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (v : Fin (n+1)) :
    MarkedMemoryHistoryTraceBirth hZ history (2*v.val) =
      MarkedMemoryGhostBirthIndex (markedMemoryHistoryVertexGhost hZ history v) := by
  induction n generalizing s with
  | zero => have hv : v = 0 := Fin.eq_zero v; subst v; rfl
  | succ n ih =>
    refine Fin.cases ?_ (fun w => ?_) v
    · rfl
    · have hw : (w.succ : ℕ) = w.val+1 := rfl
      have ht : 2*(w.succ.val) = 2*w.val+2 := by omega
      rw [ht]
      exact ih history.2.2 w

theorem markedMemoryHistoryVertexGhost_step {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (v : Fin (n+1)) :
    HEq (markedMemoryHistoryTraceStep hZ history (2*v.val))
      (markedMemoryGhostPopulationOrigin hZ (markedMemoryHistoryVertexState hZ history v)
        (markedMemoryHistoryVertexGhost hZ history v)) := by
  induction n generalizing s with
  | zero => have hv : v = 0 := Fin.eq_zero v; subst v; rfl
  | succ n ih =>
    refine Fin.cases ?_ (fun w => ?_) v
    · rfl
    · have hw : (w.succ : ℕ) = w.val+1 := rfl
      have ht : 2*(w.succ.val) = 2*w.val+2 := by omega
      rw [ht]
      exact ih history.2.2 w

end
end ArtinMatthews
