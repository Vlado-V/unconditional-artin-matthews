module

public import ArtinMatthews.MarkedMemoryPathSlotPairs
public import ArtinMatthews.MarkedPhysicalCoordinateIndexActivePath
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

/-! The canonical physical copy index of an active path keeps precisely
one free ordering of copied slots per band and edge. No kernel support
condition is needed to construct the index. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime)
  {pads n R : ℕ}

def markedPhysicalCoordinateIndexOutgoing
    (i : MarkedPhysicalCoordinateIndex P (pads+1) n R) (v : Fin n) (j : J) :
    markedRawPrimeBand (P j) :=
  markedPhysicalCoordinateIndexRawActive P hP pads i v.castSucc j ((i.2.2 v).1 j (Fin.last pads))

def markedPhysicalCoordinateIndexIncoming
    (i : MarkedPhysicalCoordinateIndex P (pads+1) n R) (v : Fin n) (j : J) :
    markedRawPrimeBand (P j) :=
  markedPhysicalCoordinateIndexRawActive P hP pads i v.succ j ((i.2.2 v).2 j (Fin.last pads))

variable (d : MarkedMemoryActivePathData (fun j => markedRawPrimeBand (P j)) pads (markedPrimitiveCoordinateTube R) n)
  (order : Fin n → J → Equiv.Perm (Fin pads))

def markedPhysicalActivePathIndex : MarkedPhysicalCoordinateIndex P (pads+1) n R :=
  (fun v => markedPhysicalMarkingEquiv P hP (pads+1) (fun j k => d.active v j k),
    (fun v => d.position v.succ,
      fun v => (fun j => (markedMemoryPathSlotPair d v j (order v j)).1.1,
        fun j => (markedMemoryPathSlotPair d v j (order v j)).1.2.symm)))

omit [Fintype J] [DecidableEq J] in
theorem markedPhysicalActivePathIndex_path (hinit : (d.position 0).1=(1,0)) (v : Fin (n+1)) :
    markedPhysicalCoordinateIndexPath (markedPhysicalActivePathIndex P hP d order).2.1 v=(d.position v).1 := by
  cases v using Fin.cases with
  | zero => simpa only [markedPhysicalActivePathIndex,markedPhysicalCoordinateIndexPath,Fin.cons_zero] using hinit.symm
  | succ v => rfl

omit [Fintype J] [DecidableEq J] in
theorem markedPhysicalActivePathIndex_rawActive (v : Fin (n+1)) (j : J) (k : Fin (pads+1)) :
    markedPhysicalCoordinateIndexRawActive P hP pads (markedPhysicalActivePathIndex P hP d order) v j k=
      d.active v j k := rfl

omit [Fintype J] [DecidableEq J] in
theorem markedPhysicalActivePathIndex_outgoing (v : Fin n) (j : J) :
    markedPhysicalCoordinateIndexOutgoing P hP (markedPhysicalActivePathIndex P hP d order) v j=d.outgoing v j :=
  markedMemoryPathSlotPair_source_last d v j (order v j)

omit [Fintype J] [DecidableEq J] in
theorem markedPhysicalActivePathIndex_incoming (v : Fin n) (j : J) :
    markedPhysicalCoordinateIndexIncoming P hP (markedPhysicalActivePathIndex P hP d order) v j=d.incoming v j :=
  markedMemoryPathSlotPair_target_last d v j (order v j)

omit [Fintype J] [DecidableEq J] in
theorem markedPhysicalActivePathIndex_distinct (v : Fin (n+1)) :
    MarkedPhysicalMarkingDistinct ((markedPhysicalActivePathIndex P hP d order).1 v) := by
  apply (markedPhysicalMarkingEquiv_distinct P hP (pads+1) _).mpr
  exact fun j => (d.active v j).injective

end
end ArtinMatthews
