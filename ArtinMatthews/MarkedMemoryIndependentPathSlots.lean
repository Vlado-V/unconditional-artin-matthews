module

public import ArtinMatthews.MarkedMemoryPathSlotPairs
public import ArtinMatthews.MarkedMemoryIndependentActivePath
public import ArtinMatthews.MarkedMemoryIndependentEdge
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

/-! The independent tableau's actual copied-slot pair is exactly the
canonical pair on its derived raw-prime active path. Numeric injectivity
is used through the genuine derived path embeddings. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (hinj : Function.Injective (markedMemoryIndependentPrime hZ d))

local notation "path" => markedMemoryIndependentActivePath hZ d hinj

theorem markedMemoryIndependent_path_outgoingSlot (v : Fin n) (j : J) :
    markedMemoryIndependentOutgoing hZ d v.val v.2 j=markedMemoryPathOutgoingSlot path v j := by
  apply ((path).active v.castSucc j).injective
  calc
    _ = (d.particle j ((d.lifespan j).outgoing (2*v.val+1))).1 :=
      congrArg (fun a => (d.particle j a).1) (markedMemoryIndependentOutgoing_eq hZ d v.val v.2 j)
    _ = (path).outgoing v j := rfl
    _ = _ := (markedMemoryPathOutgoingSlot_eq path v j).symm

theorem markedMemoryIndependent_path_incomingSlot (v : Fin n) (j : J) :
    markedMemoryIndependentIncoming hZ d v.val v.2 j=markedMemoryPathIncomingSlot path v j := by
  apply ((path).active v.succ j).injective
  calc
    _ = (d.particle j ((d.lifespan j).incoming (2*v.val+1))).1 :=
      congrArg (fun a => (d.particle j a).1) (markedMemoryIndependentIncoming_eq hZ d v.val v.2 j)
    _ = (path).incoming v j := rfl
    _ = _ := (markedMemoryPathIncomingSlot_eq path v j).symm

theorem markedMemoryIndependent_path_sourceSlots (v : Fin n) (order : J → Equiv.Perm (Fin pads)) (j : J) :
    markedMemoryIndependentSourceSlots hZ d v.val v.2 order j=
      (markedMemoryPathSlotPair path v j (order j)).1.1 := by
  change markedMemoryOutgoingSlotPermutation (markedMemoryIndependentOutgoing hZ d v.val v.2 j) (order j)=
    markedMemoryOutgoingSlotPermutation (markedMemoryPathOutgoingSlot path v j) (order j)
  rw [markedMemoryIndependent_path_outgoingSlot]

theorem markedMemoryIndependent_path_targetSlots (v : Fin n) (order : J → Equiv.Perm (Fin pads)) (j : J) :
    markedMemoryIndependentTargetSlots hZ d v.val v.2 order j=
      (markedMemoryPathSlotPair path v j (order j)).1.2 := by
  have hc : MarkedMemorySlotPairCompatible ((path).active v.castSucc j) ((path).active v.succ j)
      (markedMemoryPathOutgoingSlot path v j) (markedMemoryPathIncomingSlot path v j)
      (markedMemoryIndependentSourceSlots hZ d v.val v.2 order j,
        markedMemoryIndependentTargetSlots hZ d v.val v.2 order j) := by
    refine ⟨?_,?_,?_⟩
    · exact (markedMemoryIndependentSlotPairs hZ d v.val v.2 order j).2.1 |>.trans
        (markedMemoryIndependent_path_outgoingSlot hZ d hinj v j)
    · rw [← markedMemoryIndependent_path_incomingSlot hZ d hinj v j]
      exact (markedMemoryIndependentSlotPairs hZ d v.val v.2 order j).2.2.1
    · intro k
      exact congrArg (fun a => (d.particle j a).1)
        ((markedMemoryIndependentSlotPairs hZ d v.val v.2 order j).2.2.2 k)
  have hp := markedMemorySlotPairCompatible_eq_of_source ((path).active v.castSucc j) ((path).active v.succ j)
    (markedMemoryPathOutgoingSlot path v j) (markedMemoryPathIncomingSlot path v j) hc
    (markedMemoryPathSlotPair path v j (order j)).2
    (markedMemoryIndependent_path_sourceSlots hZ d hinj v order j)
  exact congrArg Prod.snd hp

end
end ArtinMatthews
