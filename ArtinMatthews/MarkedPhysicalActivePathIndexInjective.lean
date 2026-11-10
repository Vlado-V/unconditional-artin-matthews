module

public import ArtinMatthews.MarkedPhysicalActivePathIndex
public import ArtinMatthews.MarkedMemoryActivePathFinite
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

/-! The canonical coordinate index recovers the entire active path and
its free copied-slot ordering. This is a genuine injection, including
zero determinants and repeated position visits. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime)
  {pads n R : ℕ}
  {d e : MarkedMemoryActivePathData (fun j => markedRawPrimeBand (P j)) pads (markedPrimitiveCoordinateTube R) n}
  {order orders : Fin n → J → Equiv.Perm (Fin pads)}

omit [Fintype J] [DecidableEq J] in
theorem markedPhysicalActivePathIndex_path_injective
    (hd : (d.position 0).1=(1,0)) (he : (e.position 0).1=(1,0))
    (h : markedPhysicalActivePathIndex P hP d order=markedPhysicalActivePathIndex P hP e orders) : d=e := by
  apply markedMemoryActivePath_ext
  · funext v
    apply Subtype.ext
    exact (markedPhysicalActivePathIndex_path P hP d order hd v).symm.trans
      ((congrArg (fun i : MarkedPhysicalCoordinateIndex P (pads+1) n R =>
        markedPhysicalCoordinateIndexPath i.2.1 v) h).trans
        (markedPhysicalActivePathIndex_path P hP e orders he v))
  · funext v j
    apply Function.Embedding.ext
    intro k
    exact (markedPhysicalActivePathIndex_rawActive P hP d order v j k).symm.trans
      ((congrArg (fun i : MarkedPhysicalCoordinateIndex P (pads+1) n R =>
        markedPhysicalCoordinateIndexRawActive P hP pads i v j k) h).trans
        (markedPhysicalActivePathIndex_rawActive P hP e orders v j k))
  · funext v j
    exact (markedPhysicalActivePathIndex_incoming P hP d order v j).symm.trans
      ((congrArg (fun i : MarkedPhysicalCoordinateIndex P (pads+1) n R =>
        markedPhysicalCoordinateIndexIncoming P hP i v j) h).trans
        (markedPhysicalActivePathIndex_incoming P hP e orders v j))
  · funext v j
    exact (markedPhysicalActivePathIndex_outgoing P hP d order v j).symm.trans
      ((congrArg (fun i : MarkedPhysicalCoordinateIndex P (pads+1) n R =>
        markedPhysicalCoordinateIndexOutgoing P hP i v j) h).trans
        (markedPhysicalActivePathIndex_outgoing P hP e orders v j))

omit [Fintype J] [DecidableEq J] in
theorem markedPhysicalActivePathIndex_order_injective
    (h : markedPhysicalActivePathIndex P hP d order=markedPhysicalActivePathIndex P hP d orders) : order=orders := by
  funext v j
  have hc := congrArg (fun i : MarkedPhysicalCoordinateIndex P (pads+1) n R => i.2.2 v) h
  have hp : markedMemoryPathSlotPair d v j (order v j)=markedMemoryPathSlotPair d v j (orders v j) := by
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun c => c.1 j) hc
    · have ht := congrArg (fun c => c.2 j) hc
      change (markedMemoryPathSlotPair d v j (order v j)).1.2.symm=
        (markedMemoryPathSlotPair d v j (orders v j)).1.2.symm at ht
      simpa only [Equiv.symm_symm] using congrArg Equiv.symm ht
  exact markedMemorySlotFiberOfOrder_injective (d.active v.castSucc j) (d.active v.succ j)
    (markedMemoryPathOutgoingSlot d v j) (markedMemoryPathIncomingSlot d v j)
    (markedMemoryPathActive_remaining d v j) hp

end
end ArtinMatthews
