module

public import ArtinMatthews.MarkedMemoryActualQueueData
public import ArtinMatthews.MarkedMemoryActualEdgeQueue
public import ArtinMatthews.MarkedMemoryActualGhostQueue
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
public import Mathlib.RingTheory.WittVector.IsPoly
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

/-! The independently reconstructed queue equals the literal ordered
pending queue at every bounded half-step of the original history. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)

theorem markedMemoryActualQueueData_order (t : ℕ) (ht : t ≤ 2*n+1) (j : J) :
    markedMemoryPendingQueueAt (markedMemoryActualQueueData hZ history j) t =
      markedMemoryActualPendingQueue hZ history t j := by
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases he : t % 2 = 0
    · simp only [markedMemoryPendingQueueAt,he,ite_true]
      change markedMemoryGhostQueue (markedMemoryPendingQueueAt (markedMemoryActualQueueData hZ history j) t)
        (markedMemoryActualBirthQueue hZ history t j) (markedMemoryActualLast hZ history j) t = _
      rw [ih (by omega)]
      let v : Fin (n+1) := ⟨t/2,by omega⟩
      have hv : markedMemoryHistoryGhostTime n v = t := by
        rw [markedMemoryHistoryGhostTime_eq]
        change 2*(t/2) = t
        omega
      simpa only [hv] using (markedMemoryActualGhost_queue hZ history v j).symm
    · have ho : t % 2 = 1 := by omega
      simp only [markedMemoryPendingQueueAt,he,ite_false]
      change markedMemoryEdgeQueue (markedMemoryPendingQueueAt (markedMemoryActualQueueData hZ history j) t)
        (markedMemoryActualIncomingAt hZ history t j) (markedMemoryActualOutgoingAt hZ history t j)
        (decide (t < markedMemoryActualLast hZ history j (markedMemoryActualOutgoingAt hZ history t j))) = _
      rw [ih (by omega)]
      obtain ⟨v,hv⟩ := markedMemoryActualOddIndex (n := n) t (by omega) ho
      rw [hv,markedMemoryActualIncomingAt_edge,markedMemoryActualOutgoingAt_edge]
      exact (markedMemoryActualEdge_queue hZ history v j).symm

end
end ArtinMatthews
