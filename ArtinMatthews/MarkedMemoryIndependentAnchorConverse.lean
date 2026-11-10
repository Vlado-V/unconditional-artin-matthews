module

public import ArtinMatthews.MarkedMemoryHistoryAnchorGates
public import ArtinMatthews.MarkedMemoryIndependentHistory
public import ArtinMatthews.MarkedMemoryIndependentMarks
public import ArtinMatthews.MarkedMemoryAnchorVertexCriterion
public import ArtinMatthews.MarkedMemoryCopiedLineConverse
public import ArtinMatthews.MarkedMemoryIndependentChoiceAccess
public import ArtinMatthews.MarkedMemoryTransitionDeterminismAccessors
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

/-! Distinct static primes and the actual active-anchor incidences imply
all copied-product gates of the independently assembled history. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (hinj : Function.Injective (markedMemoryIndependentPrime hZ d))
  (hl : ∀ (v : Fin (n+1)) j k,(d.particle j (d.activeId v.val j k)).2=
    markedPrimePositionLine ((d.particle j (d.activeId v.val j k)).1.1 : ℕ)
      (d.position v.val).1 (hZ _ (d.position v.val).2))

include hinj hl

theorem markedMemoryIndependent_edge_anchor_of_active_lines
    (v : Fin n) (order : J → Equiv.Perm (Fin pads)) :
    MarkedMemoryEdgeAnchorGate hZ _ (markedMemoryIndependentEdge hZ d v.val v.2 order) := by
  change (markedRawCopiedProduct
    (fun j (k : Fin pads) =>
      (d.particle j (d.activeId v.val j (markedMemoryIndependentSourceSlots hZ d v.val v.2 order j k.castSucc))).1) : ℤ) ∣
    markedMinorIntegerDet (d.position v.val).1 (d.position (v.val+1)).1
  refine markedMemoryCopiedProduct_dvd_of_lines _ ?_ _ _
    (hZ _ (d.position v.val).2) (hZ _ (d.position (v.val+1)).2) ?_
  · intro a b hab
    have hid := hinj (show markedMemoryIndependentPrime hZ d
      ⟨a.1,d.activeId v.val a.1 (markedMemoryIndependentSourceSlots hZ d v.val v.2 order a.1 a.2.castSucc)⟩=
      markedMemoryIndependentPrime hZ d
      ⟨b.1,d.activeId v.val b.1 (markedMemoryIndependentSourceSlots hZ d v.val v.2 order b.1 b.2.castSucc)⟩ from hab)
    have hj : a.1=b.1 := (Sigma.mk.inj hid).1
    rcases a with ⟨j,k⟩
    rcases b with ⟨j',l⟩
    dsimp at hj
    subst j'
    have hkl : k=l := by
      apply Fin.castSucc_injective
      apply (markedMemoryIndependentSourceSlots hZ d v.val v.2 order j).injective
      apply (d.activeId v.val j).injective
      exact eq_of_heq (Sigma.mk.inj hid).2
    cases hkl
    rfl
  · intro j k
    have hm := (markedMemoryIndependentSlotPairs hZ d v.val v.2 order j).2.2.2 k
    have hs := hl v.castSucc j
      (markedMemoryIndependentSourceSlots hZ d v.val v.2 order j k.castSucc)
    have ht := hl v.succ j
      ((markedMemoryIndependentTargetSlots hZ d v.val v.2 order j).symm k.castSucc)
    change (d.particle j (d.activeId v.val j
      (markedMemoryIndependentSourceSlots hZ d v.val v.2 order j k.castSucc))).2=_ at hs
    simp only [Fin.val_succ] at ht
    change d.activeId v.val j
      (markedMemoryIndependentSourceSlots hZ d v.val v.2 order j k.castSucc)=
      d.activeId (v.val+1) j
        ((markedMemoryIndependentTargetSlots hZ d v.val v.2 order j).symm k.castSucc) at hm
    have htransfer (a b : A j) (he : a=b) :
        ((d.particle j b).2=markedPrimePositionLine ((d.particle j b).1.1 : ℕ)
          (d.position (v.val+1)).1 (hZ _ (d.position (v.val+1)).2)) →
        ((d.particle j a).2=markedPrimePositionLine ((d.particle j a).1.1 : ℕ)
          (d.position (v.val+1)).1 (hZ _ (d.position (v.val+1)).2)) := by
      cases he
      exact id
    exact hs.symm.trans (htransfer _ _ hm ht)

theorem markedMemoryIndependent_history_anchor_of_active_lines
    (order : Fin n → J → Equiv.Perm (Fin pads)) :
    MarkedMemoryHistoryAnchorAdmissible hZ (markedMemoryIndependentHistory hZ d order) := by
  apply (markedMemoryHistoryAnchorAdmissible_iff_vertices hZ _).mpr
  intro v
  apply (markedMemoryEdgeAnchorGate_heq hZ
    (markedMemoryIndependent_vertex_edge_source hZ d order v) _ _
    (markedMemoryFiniteTransitions_history_vertexEdge hZ (markedMemoryIndependentTransitions hZ d order) v)).mpr
  change MarkedMemoryEdgeAnchorGate hZ _
    (markedMemoryEdgeTransport hZ (markedMemoryIndependentGhost_target hZ d v.val (Nat.le_of_lt v.2)).symm
      (markedMemoryIndependentEdge hZ d v.val v.2 (order v)))
  rw [markedMemoryEdgeTransport_anchorGate]
  exact markedMemoryIndependent_edge_anchor_of_active_lines hZ d hinj hl v (order v)

end
end ArtinMatthews
