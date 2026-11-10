module

public import ArtinMatthews.MarkedMemoryActualTableau
public import ArtinMatthews.MarkedMemoryActualStateReconstruction
public import ArtinMatthews.MarkedMemoryGhostChoiceRecovery
public import ArtinMatthews.MarkedMemoryQueueOriginLabels
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The independently reconstructed ghost is the original literal
choice, including its ordered birth tuple. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)
  (ha : MarkedMemoryHistoryAnchorAdmissible hZ history)

local notation "tableau" => markedMemoryActualTableau hZ history ha
local notation "vertex" v:max => markedMemoryHistoryVertexState hZ history v
local notation "ghost" v:max => markedMemoryHistoryVertexGhost hZ history v

theorem markedMemoryActualTableau_ghost_source (v : Fin (n+1)) :
    markedMemoryIndependentState hZ tableau v.val (by omega) = vertex v :=
  (markedMemoryActualTableau_state hZ history ha v.val (by omega)).trans
    (markedMemoryHistoryVertexState_trace hZ history v)

theorem markedMemoryActualTableau_ghost_heq (v : Fin (n+1)) :
    HEq (markedMemoryIndependentGhost hZ tableau v.val (by omega)) (ghost v) := by
  let c := markedMemoryIndependentGhost hZ tableau v.val (by omega)
  let hs := markedMemoryActualTableau_ghost_source hZ history ha v
  have hd : (markedMemoryGhostTransport hZ hs c).deletion = (ghost v).deletion := by
    funext j
    apply Finset.ext
    intro k
    rw [markedMemoryGhostTransport_deletion_mem]
    let q := markedMemoryIndependentQueue hZ tableau (2*v.val) j
    let i : Fin q.length := Fin.cast
      (congrArg (fun r : MarkedRawState P (pads+1) B Z => (r.2.2.1.1 j : ℕ)) hs.symm) k
    have ht : markedMemoryHistoryGhostTime n v = 2*v.val := markedMemoryHistoryGhostTime_eq n v
    have hq : q = List.ofFn (markedMemoryActualGhostSourceIds hZ history v j) := by
      exact (markedMemoryActualTableau_queue hZ history ha (2*v.val) (by omega) j).trans
        (by simpa only [ht] using (markedMemoryActualGhostSourceIds_list hZ history v j).symm)
    have hi := markedMemoryListGet_ofFn_eq (markedMemoryActualGhostSourceIds hZ history v j) q hq.symm i
    have hk : Fin.cast (by rw [hq,List.length_ofFn]) i = k := Fin.ext rfl
    rw [hk] at hi
    change i ∈ markedMemoryGhostQueueDeletion (markedMemoryIndependentQueue hZ tableau (2*v.val))
      (fun j => ((tableau).lifespan j).last) (2*v.val) j ↔ k ∈ (ghost v).deletion j
    simp only [markedMemoryGhostQueueDeletion,Finset.mem_filter,Finset.mem_univ,true_and]
    change markedMemoryActualLast hZ history j (q.get i) = 2*v.val ↔ k ∈ (ghost v).deletion j
    rw [hi]
    simpa only [ht] using (markedMemoryActualGhost_deleted_iff hZ history v j k).symm
  have ht : markedMemoryGhostChoiceTarget hZ (vertex v) (markedMemoryGhostTransport hZ hs c) =
      markedMemoryGhostChoiceTarget hZ (vertex v) (ghost v) := by
    rw [markedMemoryGhostTransport_target]
    exact (markedMemoryIndependentGhost_target hZ tableau v.val (by omega)).trans
      ((markedMemoryActualTableau_postGhost hZ history ha v.val (by omega)).trans
        (by simpa only [markedMemoryHistoryGhostTime_eq] using markedMemoryHistoryGhostTarget_trace hZ history v))
  have hc := markedMemoryGhostChoice_eq_of_deletion_target hZ (markedMemoryGhostTransport hZ hs c) (ghost v) hd ht
  exact (markedMemoryGhostTransport_heq hZ hs c).trans (heq_of_eq hc)

end
end ArtinMatthews
