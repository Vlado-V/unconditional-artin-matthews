module

public import ArtinMatthews.MarkedMemoryPivotValueDefs
public import ArtinMatthews.MarkedMemoryPrefixMemo
public import ArtinMatthews.MarkedMemoryStageMemo
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Local ghost and edge choices update an arbitrary global memo at
their true offset. Only the values at this operation are required;
the initial address carrier and all earlier values stay fixed. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {M B N pads : ℕ} {Z : Finset (ℤ × ℤ)}

theorem markedMemoryGhostPivotValues_memo
    (hZ : ∀ z∈Z,IsCoprime z.1 z.2) {s : MarkedRawState P M B Z}
    (ghost : MarkedMemoryGhostChoice hZ s) (t : Fin (N+1))
    (v : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes)
    (hv : ∀ j k,v (Sum.inr (Sum.inl ⟨t,j,k⟩))=markedMemoryGhostPotentialValue ghost j k) :
    markedMemoryGhostPivotValues t (markedMemoryPotentialMemo v (2*t.val+1))
      ghost.sizes.1 ghost.births=markedMemoryPotentialMemo v ((2*t.val+1)+1) := by
  classical
  unfold markedMemoryGhostPivotValues
  apply markedMemoryStageBirthValues_memo
  · intro a
    rfl
  · intro a
    change v (Sum.inr (Sum.inl ⟨t,a.1,
      ⟨a.2.val,a.2.2.trans_le (Nat.le_of_lt_succ (ghost.sizes.1 a.1).2)⟩⟩))=
      some ((ghost.births a.1 a.2).1)
    exact (hv _ _).trans (markedMemoryGhostPotentialValue_birth ghost a.1 a.2)
  · intro a ht hn
    rcases a with ⟨j,k⟩ | ⟨w,j,k⟩ | ⟨w,j⟩
    · simp only [markedMemoryPotentialChronologicalTime] at ht
      omega
    · have hw : w=t := Fin.ext (by
        simp only [markedMemoryPotentialChronologicalTime] at ht
        omega)
      subst w
      have hk : ¬k.val < (ghost.sizes.1 j:ℕ) := by
        intro hk
        exact hn (markedMemoryStageDraw_mem _ (markedMemoryGhostStageDraw_injective t _)
          ⟨j,⟨k.val,hk⟩⟩)
      rw [hv,markedMemoryGhostPotentialValue,dite_eq_right hk]
    · simp only [markedMemoryPotentialChronologicalTime] at ht
      omega

theorem markedMemoryEdgePivotValues_memo
    (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (edge : MarkedRawEdgeChoice hZ s) (t : Fin N)
    (v : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes)
    (hv : ∀ j,v (Sum.inr (Sum.inr ⟨t,j⟩))=
      if edge.promotions j=none then
        some ((markedRawEdgeTargetLast s.2.2 edge.promotions edge.fresh j).1) else none) :
    markedMemoryEdgePivotValues t (markedMemoryPotentialMemo v (2*t.val+2)) hZ s edge=
      markedMemoryPotentialMemo v ((2*t.val+2)+1) := by
  classical
  unfold markedMemoryEdgePivotValues
  apply markedMemoryStageBirthValues_memo
  · intro i
    rfl
  · intro i
    have hi : edge.promotions i.1=none := by
      by_contra hn
      exact (Finset.mem_sdiff.mp i.2).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩)
    change v (Sum.inr (Sum.inr ⟨t,i.1⟩))=
      some ((markedRawEdgeTargetLast s.2.2 edge.promotions edge.fresh i.1).1)
    exact (hv i.1).trans (ite_eq_left hi)
  · intro a ht hn
    rcases a with ⟨j,k⟩ | ⟨w,j,k⟩ | ⟨w,j⟩
    · simp only [markedMemoryPotentialChronologicalTime] at ht
      omega
    · simp only [markedMemoryPotentialChronologicalTime] at ht
      omega
    · have hw : w=t := Fin.ext (by
        simp only [markedMemoryPotentialChronologicalTime] at ht
        omega)
      subst w
      have hp : edge.promotions j≠none := by
        intro hp
        apply hn
        have hj : j∉markedDirtyEdgePromotedGroups edge.promotions := by
          simp [markedDirtyEdgePromotedGroups,hp]
        exact markedMemoryStageDraw_mem _ (markedMemoryEdgeStageDraw_injective t _)
          ⟨j,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hj⟩⟩
      rw [hv,ite_eq_right hp]

end
end ArtinMatthews
