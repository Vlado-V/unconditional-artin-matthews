module

public import ArtinMatthews.MarkedMemoryActivePathData
public import ArtinMatthews.MarkedMemoryLifespanSlotFiber
public import ArtinMatthews.MarkedMemoryLifespanSlotExchange
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! Compatible physical copy pairs on an active path have exactly the
original free ordering of its copied slots. The target member here uses
the memory convention; the physical copy is its inverse. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

theorem markedMemorySlotPairCompatible_eq_of_source
    {A : Type*} {pads : ℕ} (src dst : Fin (pads+1) ↪ A) (out inc : Fin (pads+1))
    {a b : Equiv.Perm (Fin (pads+1)) × Equiv.Perm (Fin (pads+1))}
    (ha : MarkedMemorySlotPairCompatible src dst out inc a)
    (hb : MarkedMemorySlotPairCompatible src dst out inc b) (hs : a.1=b.1) : a=b := by
  apply Prod.ext hs
  have ht : a.2.symm=b.2.symm := by
    apply Equiv.ext
    intro k
    refine Fin.lastCases ?_ (fun l => ?_) k
    · have h₁ : a.2.symm (Fin.last pads)=inc := by
        apply a.2.injective
        rw [Equiv.apply_symm_apply,ha.2.1]
      have h₂ : b.2.symm (Fin.last pads)=inc := by
        apply b.2.injective
        rw [Equiv.apply_symm_apply,hb.2.1]
      exact h₁.trans h₂.symm
    · apply dst.injective
      exact (ha.2.2 l).symm.trans
        ((congrArg (fun σ : Equiv.Perm (Fin (pads+1)) => src (σ l.castSucc)) hs).trans (hb.2.2 l))
  simpa only [Equiv.symm_symm] using congrArg Equiv.symm ht

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads n : ℕ} {Z : Finset (ℤ × ℤ)}
  (d : MarkedMemoryActivePathData P pads Z n)

def markedMemoryPathOutgoingSlot (v : Fin n) (j : J) : Fin (pads+1) :=
  Classical.choose (d.outgoing_present v j)

def markedMemoryPathIncomingSlot (v : Fin n) (j : J) : Fin (pads+1) :=
  Classical.choose (d.incoming_present v j)

omit [Fintype J] in
theorem markedMemoryPathOutgoingSlot_eq (v : Fin n) (j : J) :
    d.active v.castSucc j (markedMemoryPathOutgoingSlot d v j)=d.outgoing v j :=
  Classical.choose_spec (d.outgoing_present v j)

omit [Fintype J] in
theorem markedMemoryPathIncomingSlot_eq (v : Fin n) (j : J) :
    d.active v.succ j (markedMemoryPathIncomingSlot d v j)=d.incoming v j :=
  Classical.choose_spec (d.incoming_present v j)

omit [Fintype J] in
theorem markedMemoryPathActive_remaining (v : Fin n) (j : J) :
    (markedMemoryBirthBatch (d.active v.castSucc j)).erase
      (d.active v.castSucc j (markedMemoryPathOutgoingSlot d v j))=
    (markedMemoryBirthBatch (d.active v.succ j)).erase
      (d.active v.succ j (markedMemoryPathIncomingSlot d v j)) := by
  apply markedMemoryActiveExchange_remaining
  intro p
  rw [markedMemoryPathOutgoingSlot_eq,markedMemoryPathIncomingSlot_eq]
  exact d.exchange v j p

def markedMemoryPathSlotPair (v : Fin n) (j : J) (order : Equiv.Perm (Fin pads)) :
    MarkedMemorySlotPairFiber (d.active v.castSucc j) (d.active v.succ j)
      (markedMemoryPathOutgoingSlot d v j) (markedMemoryPathIncomingSlot d v j) :=
  markedMemorySlotFiberOfOrder _ _ _ _ (markedMemoryPathActive_remaining d v j) order

omit [Fintype J] in
theorem markedMemoryPathSlotPair_source_last (v : Fin n) (j : J) (order : Equiv.Perm (Fin pads)) :
    d.active v.castSucc j ((markedMemoryPathSlotPair d v j order).1.1 (Fin.last pads))=d.outgoing v j := by
  rw [(markedMemoryPathSlotPair d v j order).2.1,markedMemoryPathOutgoingSlot_eq]

omit [Fintype J] in
theorem markedMemoryPathSlotPair_target_last (v : Fin n) (j : J) (order : Equiv.Perm (Fin pads)) :
    d.active v.succ j ((markedMemoryPathSlotPair d v j order).1.2.symm (Fin.last pads))=d.incoming v j := by
  have h : (markedMemoryPathSlotPair d v j order).1.2.symm (Fin.last pads)=
      markedMemoryPathIncomingSlot d v j := by
    apply (markedMemoryPathSlotPair d v j order).1.2.injective
    rw [Equiv.apply_symm_apply,(markedMemoryPathSlotPair d v j order).2.2.1]
  rw [h,markedMemoryPathIncomingSlot_eq]

end
end ArtinMatthews
