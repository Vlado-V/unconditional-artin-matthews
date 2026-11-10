module

public import ArtinMatthews.MarkedPhysicalMemoryHistoryIndex
public import ArtinMatthews.MarkedPhysicalActivePathIndex
public import ArtinMatthews.MarkedMemoryHistorySlotSchedule
public import ArtinMatthews.MarkedMemoryIndependentActivePath
public import ArtinMatthews.MarkedMemoryIndependentHistory
public import ArtinMatthews.MarkedMemoryIndependentChoiceAccess
public import ArtinMatthews.MarkedMemoryIndependentOrderMultiplicity
public import ArtinMatthews.MarkedMemoryIndependentPathSlots
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

/-! Reconstructing the coordinate index of an independent history loses
no copy coordinate: it is exactly the canonical index of its derived
active path and the same free ordering. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)

theorem markedMemoryHistoryVertexEdge_sourceSlots
    {s : MarkedRawState P (pads+1) B Z} (H : MarkedMemoryChronologicalHistory hZ n s) (v : Fin n) :
    (markedMemoryHistoryVertexEdge hZ H v).1=markedMemoryHistorySourceSlots hZ H v := by
  induction n generalizing s with
  | zero => exact Fin.elim0 v
  | succ n ih =>
    refine Fin.cases ?_ (fun w => ?_) v
    · rfl
    · exact ih H.2.2 w

variable [DecidableEq J] (PN : J → Finset ℕ) (hP : ∀ j p,p∈PN j → p.Prime)
  {R : ℕ} (hT : ∀ z∈markedPrimitiveCoordinateTube R,IsCoprime z.1 z.2)

omit [DecidableEq J] in
theorem markedPhysicalMemoryHistoryIndex_transport
    {s t : MarkedRawState (fun j => markedRawPrimeBand (PN j)) (pads+1) B (markedPrimitiveCoordinateTube R)}
    (hs : s=t) (H : MarkedMemoryChronologicalHistory hT n s) :
    markedPhysicalMemoryHistoryIndex PN hP hT (markedMemoryHistoryTransport hT hs H)=
      markedPhysicalMemoryHistoryIndex PN hP hT H := by
  cases hs
  rfl

variable {A : J → Type*} [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  (d : MarkedMemoryIndependentLifespans (A := A) (P := fun j => markedRawPrimeBand (PN j))
    (pads := pads) (B := B) hT n)
  (hinj : Function.Injective (markedMemoryIndependentPrime hT d))
  (order : Fin n → J → Equiv.Perm (Fin pads))

omit [DecidableEq J] in
theorem markedPhysicalMemoryHistoryIndex_independent :
    markedPhysicalMemoryHistoryIndex PN hP hT (markedMemoryIndependentHistory hT d order)=
      markedPhysicalActivePathIndex PN hP (markedMemoryIndependentActivePath hT d hinj) order := by
  apply Prod.ext
  · funext v
    change markedPhysicalMarkingEquiv PN hP (pads+1)
        (markedMemoryHistoryVertexState hT (markedMemoryIndependentHistory hT d order) v).2.1=
      markedPhysicalMarkingEquiv PN hP (pads+1) (markedMemoryIndependentState hT d v.val (by omega)).2.1
    exact congrArg (fun s => markedPhysicalMarkingEquiv PN hP (pads+1) s.2.1)
      (markedMemoryIndependent_vertex_state hT d order v)
  · apply Prod.ext
    · funext v
      change (markedMemoryHistoryVertexState hT (markedMemoryIndependentHistory hT d order) v.succ).1=
        (markedMemoryIndependentState hT d v.succ.val (by omega)).1
      exact congrArg Prod.fst (markedMemoryIndependent_vertex_state hT d order v.succ)
    · funext v
      apply Prod.ext
      · funext j
        change (markedMemoryHistoryVertexEdge hT (markedMemoryIndependentHistory hT d order) v).1 j=_
        rw [markedMemoryHistoryVertexEdge_sourceSlots,markedMemoryIndependentHistory_sourceSlots]
        exact markedMemoryIndependent_path_sourceSlots hT d hinj v (order v) j
      · funext j
        change ((markedMemoryHistoryVertexEdge hT (markedMemoryIndependentHistory hT d order) v).2.2 j).symm=
          (markedMemoryPathSlotPair (markedMemoryIndependentActivePath hT d hinj) v j (order v j)).1.2.symm
        rw [markedMemoryIndependent_vertex_edge_targetSlots hT d order v]
        exact congrArg Equiv.symm (markedMemoryIndependent_path_targetSlots hT d hinj v (order v) j)

end
end ArtinMatthews
