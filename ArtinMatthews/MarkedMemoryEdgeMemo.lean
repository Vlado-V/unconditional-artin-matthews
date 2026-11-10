module

public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeFixedCode
public import ArtinMatthews.MarkedMemoryHistoryEdgeAccess
public import ArtinMatthews.MarkedMemoryPrefixMemo
public import ArtinMatthews.MarkedMemoryStageBirthMass
public import ArtinMatthews.MarkedMemoryHistoryPotentialAccess
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

/-! The actual edge inserts precisely its fresh target-last prime
labels. Promoted groups keep the potential edge address at none, while
both source and target slot permutations remain in the literal choice. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}

theorem markedMemoryHistoryMemo_edge
    (history : MarkedMemoryChronologicalHistory hZ n s) (v : Fin n) :
    let edge := markedMemoryHistoryVertexEdge hZ history v
    let pre := markedMemoryGhostChoiceTarget hZ (markedMemoryHistoryVertexState hZ history v.castSucc)
      (markedMemoryHistoryVertexGhost hZ history v.castSucc)
    let source := markedRawSlotEquiv edge.1 pre
    let I := markedDirtyEdgePromotedGroups edge.2.1.promotions
    markedMemoryStageBirthValues (2*v.val+2) (markedMemoryHistoryMemo hZ history (2*v.val+2))
      (markedMemoryEdgeStageDraw v I) (markedMemoryEdgeStageDraw_injective v I)
      (markedDirtyFixedEdgeChoiceCode hZ source I ⟨edge.2.1,rfl⟩).2.2.2=
        markedMemoryHistoryMemo hZ history ((2*v.val+2)+1) := by
  classical
  dsimp only
  let edge := markedMemoryHistoryVertexEdge hZ history v
  let pre := markedMemoryGhostChoiceTarget hZ (markedMemoryHistoryVertexState hZ history v.castSucc)
    (markedMemoryHistoryVertexGhost hZ history v.castSucc)
  let source := markedRawSlotEquiv edge.1 pre
  let I := markedDirtyEdgePromotedGroups edge.2.1.promotions
  change markedMemoryStageBirthValues (2*v.val+2) (markedMemoryHistoryMemo hZ history (2*v.val+2))
      (markedMemoryEdgeStageDraw v I) (markedMemoryEdgeStageDraw_injective v I)
      (markedDirtyFixedEdgeChoiceCode hZ source I ⟨edge.2.1,rfl⟩).2.2.2=
    markedMemoryHistoryMemo hZ history ((2*v.val+2)+1)
  apply markedMemoryStageBirthValues_memo
  · intro i
    rfl
  · intro i
    have hi : edge.2.1.promotions i.1=none := by
      by_contra hn
      exact (Finset.mem_sdiff.mp i.2).2
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩)
    change markedMemoryPotentialEdgeValue hZ history v i.1=
      some ((markedRawEdgeTargetLast source.2.2 edge.2.1.promotions edge.2.1.fresh i.1).1)
    rw [markedMemoryPotentialEdgeValue_vertex]
    exact ite_eq_left hi
  · intro a ht hn
    rcases a with ⟨j,k⟩ | ⟨w,j,k⟩ | ⟨w,j⟩
    · simp only [markedMemoryPotentialChronologicalTime] at ht
      omega
    · simp only [markedMemoryPotentialChronologicalTime] at ht
      omega
    · have hw : w=v := Fin.ext (by
        simp only [markedMemoryPotentialChronologicalTime] at ht
        omega)
      subst w
      have hp : edge.2.1.promotions j≠none := by
        intro hp
        apply hn
        have hj : j∉I := by simp [I,markedDirtyEdgePromotedGroups,hp]
        exact markedMemoryStageDraw_mem _ (markedMemoryEdgeStageDraw_injective v I)
          ⟨j,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hj⟩⟩
      change markedMemoryPotentialEdgeValue hZ history v j=none
      rw [markedMemoryPotentialEdgeValue_vertex]
      exact ite_eq_right hp

end
end ArtinMatthews
