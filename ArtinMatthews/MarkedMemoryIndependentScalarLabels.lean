module

public import ArtinMatthews.MarkedMemoryIndependentScalarEvents
public import ArtinMatthews.MarkedMemoryIndependentCorrespondence
public import ArtinMatthews.MarkedMemoryIndependentCorrespondenceGroup
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

/-! The direct old-queue and birth-list scalar events carry precisely
the supplied independent identity under the proved address equivalence. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

theorem markedMemoryFinCongr_val {m n : ℕ} (h : m = n) (i : Fin m) :
    (markedMemoryFinCongr h i).val = i.val := by
  cases h
  rfl

theorem markedMemoryGhostSourceIndex_pending {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (v : Fin (n+1)) (j : J)
    (k : Fin ((markedMemoryHistoryVertexState hZ history v).2.2.1.1 j : ℕ)) :
    markedMemoryHistoryGhostSourceIndex hZ history v (Sum.inr ⟨j,k⟩) =
      Sum.inr ⟨j,Fin.cast (congrArg (fun q : MarkedRawState P (pads+1) B Z => (q.2.2.1.1 j : ℕ))
        (markedMemoryHistoryTraceState_stage hZ history (markedMemoryHistoryVertexStage n v)).symm) k⟩ :=
  markedMemoryPopulationStateCast_pending
    (markedMemoryHistoryTraceState_stage hZ history (markedMemoryHistoryVertexStage n v)).symm j k

variable {A : J → Type*} [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)] {n : ℕ}
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (order : Fin n → J → Equiv.Perm (Fin pads))

local notation "history" => markedMemoryIndependentHistory hZ d order

theorem markedMemoryIndependentTraceBirthLabel_congr (t u : ℕ)
    (ht : t < 2*n+1) (hu : u < 2*n+1) (he : t = u)
    (b : MarkedMemoryHistoryTraceBirth hZ history t) :
    markedMemoryIndependentTraceBirthLabel hZ d order t ht b =
      markedMemoryIndependentTraceBirthLabel hZ d order u hu
        (cast (congrArg (MarkedMemoryHistoryTraceBirth hZ history) he) b) := by
  cases he
  rfl

theorem markedMemoryIndependentScalarEvents_old_label (v : Fin (n+1)) (j : J)
    (k : Fin ((markedMemoryHistoryVertexState hZ history v).2.2.1.1 j : ℕ)) :
    markedMemoryIndependentAddressEquiv hZ d order
      (markedMemoryHistoryGhostScalarOrigin hZ history ⟨v,Sum.inl ⟨j,k⟩⟩) =
    markedMemoryIndependentGhostEventLabel hZ d
      (markedMemoryIndependentScalarEventsEquiv hZ d order ⟨v,Sum.inl ⟨j,k⟩⟩) := by
  change markedMemoryIndependentAddressEquiv hZ d order
    (markedMemoryLineageOrigin (markedMemoryHistoryTraceStep hZ history) (markedMemoryHistoryGhostTime n v)
      (markedMemoryHistoryGhostSourceIndex hZ history v (Sum.inr ⟨j,k⟩))) =
    ⟨j,(markedMemoryIndependentQueue hZ d (2*v.val) j).get
      (markedMemoryFinCongr (congrArg (fun q : MarkedRawState P (pads+1) B Z => (q.2.2.1.1 j : ℕ))
        (markedMemoryIndependent_vertex_state hZ d order v)) k)⟩
  rw [markedMemoryGhostSourceIndex_pending]
  rw [markedMemoryIndependentAddress_pending_slot hZ d order (markedMemoryHistoryGhostTime n v)
    (by rw [markedMemoryHistoryGhostTime_eq]; omega)]
  apply congrArg (Sigma.mk j)
  apply markedMemoryList_get_congr
  · exact congrArg (fun t => markedMemoryIndependentQueue hZ d t j) (markedMemoryHistoryGhostTime_eq n v)
  · simp only [markedMemoryFinCongr_val]
    rfl

theorem markedMemoryIndependentScalarEvents_birth_label (v : Fin (n+1))
    (b : MarkedMemoryGhostBirthIndex (markedMemoryHistoryVertexGhost hZ history v)) :
    markedMemoryIndependentAddressEquiv hZ d order
      (markedMemoryHistoryGhostScalarOrigin hZ history ⟨v,Sum.inr b⟩) =
    markedMemoryIndependentGhostEventLabel hZ d
      (markedMemoryIndependentScalarEventsEquiv hZ d order ⟨v,Sum.inr b⟩) := by
  let mapped : MarkedMemoryGhostBirthIndex (markedMemoryIndependentGhost hZ d v.val (by omega)) :=
    (Equiv.sigmaCongrRight (fun j => markedMemoryFinCongr (markedMemoryGhostSizeEq hZ
      (markedMemoryIndependent_vertex_state hZ d order v) _ _
      (markedMemoryIndependent_vertex_ghost_heq hZ d order v) j))) b
  let b₂ : MarkedMemoryHistoryTraceBirth hZ history (2*v.val) :=
    cast (congrArg (MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryGhostTime_eq n v))
      (markedMemoryHistoryGhostTraceBirth hZ history v b)
  let b₃ : MarkedMemoryGhostBirthIndex (markedMemoryIndependentGhost hZ d v.val (by omega)) :=
    cast (markedMemoryIndependentTraceBirth_even hZ d order v.val (by omega)) b₂
  have hb₂ : HEq b₂ b := (cast_heq _ _).trans (markedMemoryGhostTraceBirth_heq hZ history v b)
  have hb₃ : HEq b₃ b := (cast_heq _ _).trans hb₂
  have hmapped : HEq mapped b := markedMemoryGhostBirthEquiv_heq hZ
    (markedMemoryIndependent_vertex_state hZ d order v) _ _
    (markedMemoryIndependent_vertex_ghost_heq hZ d order v) b
  have heq : b₃ = mapped := eq_of_heq (hb₃.trans hmapped.symm)
  change markedMemoryIndependentAddressEquiv hZ d order
      (Sum.inr ⟨markedMemoryHistoryGhostTime n v,markedMemoryHistoryGhostTraceBirth hZ history v b⟩) =
    markedMemoryIndependentGhostBirthLabel hZ d v.val (by omega) mapped
  rw [markedMemoryIndependentAddress_birth_slot hZ d order (markedMemoryHistoryGhostTime n v)
    (by rw [markedMemoryHistoryGhostTime_eq]; omega)]
  exact (markedMemoryIndependentTraceBirthLabel_congr hZ d order _ _
    (by rw [markedMemoryHistoryGhostTime_eq]; omega) (by omega) (markedMemoryHistoryGhostTime_eq n v) _).trans
      ((markedMemoryIndependentTraceBirthLabel_even hZ d order v.val (by omega) b₂).trans
        (congrArg (markedMemoryIndependentGhostBirthLabel hZ d v.val (by omega)) heq))

theorem markedMemoryIndependentScalarEvents_label (event : MarkedMemoryHistoryGhostScalarEvent hZ history) :
    markedMemoryIndependentAddressEquiv hZ d order (markedMemoryHistoryGhostScalarOrigin hZ history event) =
      markedMemoryIndependentGhostEventLabel hZ d (markedMemoryIndependentScalarEventsEquiv hZ d order event) := by
  rcases event with ⟨v,event⟩
  cases event with
  | inl old => exact markedMemoryIndependentScalarEvents_old_label hZ d order v old.1 old.2
  | inr b => exact markedMemoryIndependentScalarEvents_birth_label hZ d order v b

end
end ArtinMatthews
