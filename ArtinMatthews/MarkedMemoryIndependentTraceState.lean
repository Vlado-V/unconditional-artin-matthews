module

public import ArtinMatthews.MarkedMemoryIndependentHistory
public import ArtinMatthews.MarkedMemoryIndependentMarks
public import ArtinMatthews.MarkedMemoryPopulationTransport
public import ArtinMatthews.MarkedMemoryHistoryTrace
public import ArtinMatthews.MarkedMemoryTransitionTrace
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

/-! The reconstructed history has the independent state at every
bounded half-step. Transporting its proved population embeddings gives
actual trace labels with exactly the supplied interval support. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {n : ℕ}
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (order : Fin n → J → Equiv.Perm (Fin pads))

theorem markedMemoryIndependentHistory_trace_even (r : ℕ) (hr : r ≤ n) :
    markedMemoryHistoryTraceState hZ (markedMemoryIndependentHistory hZ d order) (2*r) =
      markedMemoryIndependentState hZ d r hr :=
  markedMemoryFiniteTransitions_history_trace_even hZ (markedMemoryIndependentTransitions hZ d order) r hr

theorem markedMemoryIndependentHistory_trace_odd (r : ℕ) (hr : r ≤ n) :
    markedMemoryHistoryTraceState hZ (markedMemoryIndependentHistory hZ d order) (2*r+1) =
      markedMemoryIndependentPostGhost hZ d r hr :=
  (markedMemoryFiniteTransitions_history_trace_odd hZ (markedMemoryIndependentTransitions hZ d order) r hr).trans
    (markedMemoryIndependentGhost_target hZ d r hr)

theorem markedMemoryIndependentStageState_congr (a b : ℕ) (ha : a ≤ 2*n+1) (hb : b ≤ 2*n+1) (h : a = b) :
    markedMemoryIndependentStageState hZ d a ha = markedMemoryIndependentStageState hZ d b hb := by
  subst b
  rfl

theorem markedMemoryIndependentHistory_trace_state (t : ℕ) (ht : t ≤ 2*n+1) :
    markedMemoryHistoryTraceState hZ (markedMemoryIndependentHistory hZ d order) t =
      markedMemoryIndependentStageState hZ d t ht := by
  have hr : t/2 ≤ n := by omega
  rcases Nat.mod_two_eq_zero_or_one t with he | he
  · have htime : t = 2*(t/2) := by omega
    exact (congrArg (markedMemoryHistoryTraceState hZ (markedMemoryIndependentHistory hZ d order)) htime).trans
      ((markedMemoryIndependentHistory_trace_even hZ d order (t/2) hr).trans
        ((markedMemoryIndependentStageState_even hZ d (t/2) hr).symm.trans
          (markedMemoryIndependentStageState_congr hZ d _ _ (by omega) ht htime.symm)))
  · have htime : t = 2*(t/2)+1 := by omega
    exact (congrArg (markedMemoryHistoryTraceState hZ (markedMemoryIndependentHistory hZ d order)) htime).trans
      ((markedMemoryIndependentHistory_trace_odd hZ d order (t/2) hr).trans
        ((markedMemoryIndependentStageState_odd hZ d (t/2) hr).symm.trans
          (markedMemoryIndependentStageState_congr hZ d _ _ (by omega) ht htime.symm)))

def markedMemoryIndependentTraceIds (t : ℕ) (ht : t ≤ 2*n+1) :
    MarkedMemoryPopulationIndex (markedMemoryHistoryTraceState hZ (markedMemoryIndependentHistory hZ d order) t) ↪ Σ j, A j :=
  (markedMemoryPopulationStateCast (markedMemoryIndependentHistory_trace_state hZ d order t ht)).toEmbedding.trans
    (markedMemoryIndependentPopulationLabel hZ d t ht)

theorem markedMemoryIndependentTraceIds_active (t : ℕ) (ht : t ≤ 2*n+1) (j : J) (k : Fin (pads+1)) :
    markedMemoryIndependentTraceIds hZ d order t ht (Sum.inl ⟨j,k⟩) =
      ⟨j,d.activeId (t/2) j k⟩ :=
  congrArg (markedMemoryIndependentPopulationLabel hZ d t ht)
    (markedMemoryPopulationStateCast_active (markedMemoryIndependentHistory_trace_state hZ d order t ht) j k)

theorem markedMemoryIndependentTraceIds_interval (t : ℕ) (ht : t ≤ 2*n+1) (a : Σ j, A j) :
    (∃ i, markedMemoryIndependentTraceIds hZ d order t ht i = a) ↔
      (d.lifespan a.1).first a.2 ≤ t ∧ t ≤ (d.lifespan a.1).last a.2 := by
  let e := markedMemoryPopulationStateCast (markedMemoryIndependentHistory_trace_state hZ d order t ht)
  constructor
  · rintro ⟨i,hi⟩
    exact (markedMemoryIndependentPopulationLabel_range hZ d t ht a).mp ⟨e i,hi⟩
  · intro ha
    obtain ⟨i,hi⟩ := (markedMemoryIndependentPopulationLabel_range hZ d t ht a).mpr ha
    exact ⟨e.symm i,(congrArg (markedMemoryIndependentPopulationLabel hZ d t ht) (e.apply_symm_apply i)).trans hi⟩

theorem markedMemoryIndependentTraceIds_prime (t : ℕ) (ht : t ≤ 2*n+1)
    (i : MarkedMemoryPopulationIndex (markedMemoryHistoryTraceState hZ (markedMemoryIndependentHistory hZ d order) t)) :
    markedMemoryIndependentPrime hZ d (markedMemoryIndependentTraceIds hZ d order t ht i) =
      markedMemoryPopulationPrime (markedMemoryHistoryTraceState hZ (markedMemoryIndependentHistory hZ d order) t) i :=
  (markedMemoryIndependentPopulationLabel_prime hZ d t ht
    (markedMemoryPopulationStateCast (markedMemoryIndependentHistory_trace_state hZ d order t ht) i)).trans
      (markedMemoryPopulationStateCast_prime (markedMemoryIndependentHistory_trace_state hZ d order t ht) i)

end
end ArtinMatthews
