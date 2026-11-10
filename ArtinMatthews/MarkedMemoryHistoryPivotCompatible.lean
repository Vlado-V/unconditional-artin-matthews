module

public import ArtinMatthews.MarkedMemoryMemoOffset
public import ArtinMatthews.MarkedMemoryPivotCompatible
public import ArtinMatthews.MarkedMemoryPrefixMemo
public import ArtinMatthews.MarkedMemoryGhostMemo
public import ArtinMatthews.MarkedMemoryShiftedMemo
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

/-! The original permutation event propagates through the actual
chronological history. Global addresses and their permutation stay fixed
when taking the local tail; only the operation offset increases. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

theorem markedMemoryMemo_stageValueGate
    {J : Type*} [Fintype J] [DecidableEq J] {M B N : ℕ}
    (v : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N))
    (hσ : MarkedBirthPermutationEvent v σ) (stage : ℕ) :
    MarkedMemoryStageValueGate σ stage (markedMemoryPotentialMemo v (stage+1)) := by
  intro a ha
  have ht := (Finset.mem_filter.mp ha).2
  have hp := markedMemoryPotentialEarlier_time (markedMemoryStageNonpivots_parent_earlier σ stage ha)
  rcases markedMemoryPotentialPivot_event σ v hσ (Finset.mem_filter.mp ha).1 with
    ⟨_,_,_,heq,hperformed⟩
  rw [markedMemoryPotentialMemo_prior v (by omega),markedMemoryPotentialMemo_prior v (by omega)]
  exact ⟨hperformed,heq⟩

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B N : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)

theorem markedMemoryHistory_initialPivotValues {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ N s) :
    markedMemoryInitialPivotValues (fun _ => none) s.2.1=markedMemoryHistoryMemo hZ history 1 := by
  have h0 : markedMemoryHistoryMemo hZ history 0=(fun _ => none) := rfl
  simpa only [markedMemoryInitialPivotValues,h0] using markedMemoryHistoryMemo_initial hZ history

theorem markedMemoryPivotCompatible_of_offsetValues
    {n j : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (hb : j+n ≤ N)
    (v : MarkedMemoryPotentialAddress J (pads+1) B N → Option Nat.Primes)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N))
    (hσ : MarkedBirthPermutationEvent v σ)
    (hv : MarkedMemoryMemoOffsetValues hZ history j hb v) :
    MarkedMemoryPivotCompatible hZ σ n j history (markedMemoryPotentialMemo v (2*j+1)) := by
  induction n generalizing j s with
  | zero =>
    have hj : j<N+1 := by omega
    refine ⟨hj,?_⟩
    have hg : ∀ i k,v (Sum.inr (Sum.inl ⟨(⟨j,hj⟩ : Fin (N+1)),i,k⟩))=
        markedMemoryGhostPotentialValue history i k := by
      intro i k
      simpa only [markedMemoryMemoGhostIndex,Fin.val_zero,Nat.add_zero,
        markedMemoryPotentialGhostValue] using hv.1 0 i k
    rw [markedMemoryGhostPivotValues_memo hZ history ⟨j,hj⟩ v hg]
    exact markedMemoryMemo_stageValueGate v σ hσ (2*j+1)
  | succ n ih =>
    have hj : j<N+1 := by omega
    have he : j<N := by omega
    refine ⟨hj,?_⟩
    dsimp only
    have hg : ∀ i k,v (Sum.inr (Sum.inl ⟨(⟨j,hj⟩ : Fin (N+1)),i,k⟩))=
        markedMemoryGhostPotentialValue history.1 i k := by
      intro i k
      simpa only [markedMemoryMemoGhostIndex,Fin.val_zero,Nat.add_zero,
        markedMemoryPotentialGhostValue,Fin.cases_zero] using hv.1 0 i k
    rw [markedMemoryGhostPivotValues_memo hZ history.1 ⟨j,hj⟩ v hg]
    refine ⟨markedMemoryMemo_stageValueGate v σ hσ (2*j+1),he,?_⟩
    dsimp only
    have hev : ∀ i,v (Sum.inr (Sum.inr ⟨(⟨j,he⟩ : Fin N),i⟩))=
        if history.2.1.2.1.promotions i=none then
          some ((markedRawEdgeTargetLast
            (markedRawSlotEquiv history.2.1.1 (markedMemoryGhostChoiceTarget hZ s history.1)).2.2
            history.2.1.2.1.promotions history.2.1.2.1.fresh i).1) else none := by
      intro i
      simpa only [markedMemoryMemoEdgeIndex,Fin.val_zero,Nat.add_zero,
        markedMemoryPotentialEdgeValue,Fin.cases_zero,markedMemoryEdgePotentialValue] using hv.2 0 i
    rw [markedMemoryEdgePivotValues_memo hZ
      (markedRawSlotEquiv history.2.1.1 (markedMemoryGhostChoiceTarget hZ s history.1))
      history.2.1.2.1 ⟨j,he⟩ v hev]
    refine ⟨markedMemoryMemo_stageValueGate v σ hσ (2*j+2),?_⟩
    rw [show (2*j+2)+1=2*(j+1)+1 by omega]
    exact ih history.2.2 (by omega) (markedMemoryMemoOffsetValues_tail hZ history hb v hv)

theorem markedMemoryHistory_pivotCompatible {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ N s)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N))
    (hσ : MarkedBirthPermutationEvent (markedMemoryPotentialAddressValue hZ history) σ) :
    MarkedMemoryPivotCompatible hZ σ N 0 history (markedMemoryHistoryMemo hZ history 1) :=
  markedMemoryPivotCompatible_of_offsetValues hZ history (by omega)
    (markedMemoryPotentialAddressValue hZ history) σ hσ (markedMemoryMemoOffsetValues_full hZ history)

end
end ArtinMatthews
