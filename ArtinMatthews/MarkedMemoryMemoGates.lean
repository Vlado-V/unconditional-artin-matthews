module

public import ArtinMatthews.MarkedMemoryHistoryEdgeAccess
public import ArtinMatthews.MarkedMemoryPrefixMemo
public import ArtinMatthews.MarkedMemoryStageBirthMass
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeFixedCode
public import ArtinMatthews.MarkedMemoryEdgeMemo
public import ArtinMatthews.MarkedMemoryGhostMemo
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

/-! The actual permutation event implies each chronological stage gate.
Every gate uses the exact memo before that stage and its literal ordered
birth tuple. The completed memo recovers all potential-address values. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}

omit [DecidableEq J] in
theorem markedMemoryHistoryMemo_full
    (history : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryHistoryMemo hZ history (2*n+2)=markedMemoryPotentialAddressValue hZ history := by
  funext a
  apply markedMemoryPotentialMemo_prior
  rcases a with ⟨j,k⟩ | ⟨t,j,k⟩ | ⟨t,j⟩ <;>
    simp only [markedMemoryPotentialChronologicalTime] <;> omega

theorem markedMemoryHistory_initial_stageGate
    (history : MarkedMemoryChronologicalHistory hZ n s)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B n))
    (hσ : MarkedBirthPermutationEvent (markedMemoryPotentialAddressValue hZ history) σ) :
    markedMemoryStageBirthGate σ 0 (markedMemoryHistoryMemo hZ history 0)
      markedMemoryInitialDraw markedMemoryInitialDraw_injective
      (fun a : Σ _j : J,Fin (pads+1) => s.2.1 a.1 a.2) := by
  apply markedMemoryStageBirthGate_of_memo_event 0 _ σ hσ
  exact markedMemoryHistoryMemo_initial hZ history

theorem markedMemoryHistory_ghost_stageGate
    (history : MarkedMemoryChronologicalHistory hZ n s)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B n))
    (hσ : MarkedBirthPermutationEvent (markedMemoryPotentialAddressValue hZ history) σ)
    (v : Fin (n+1)) :
    let ghost := markedMemoryHistoryVertexGhost hZ history v
    markedMemoryStageBirthGate σ (2*v.val+1) (markedMemoryHistoryMemo hZ history (2*v.val+1))
      (markedMemoryGhostStageDraw v ghost.sizes.1)
      (markedMemoryGhostStageDraw_injective v ghost.sizes.1)
      (fun a : Σ j,Fin (ghost.sizes.1 j:ℕ) => ghost.births a.1 a.2) := by
  dsimp only
  apply markedMemoryStageBirthGate_of_memo_event (2*v.val+1) _ σ hσ
  exact markedMemoryHistoryMemo_ghost hZ history v

theorem markedMemoryHistory_edge_stageGate
    (history : MarkedMemoryChronologicalHistory hZ n s)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B n))
    (hσ : MarkedBirthPermutationEvent (markedMemoryPotentialAddressValue hZ history) σ)
    (v : Fin n) :
    let edge := markedMemoryHistoryVertexEdge hZ history v
    let pre := markedMemoryGhostChoiceTarget hZ (markedMemoryHistoryVertexState hZ history v.castSucc)
      (markedMemoryHistoryVertexGhost hZ history v.castSucc)
    let source := markedRawSlotEquiv edge.1 pre
    let I := markedDirtyEdgePromotedGroups edge.2.1.promotions
    markedMemoryStageBirthGate σ (2*v.val+2) (markedMemoryHistoryMemo hZ history (2*v.val+2))
      (markedMemoryEdgeStageDraw v I) (markedMemoryEdgeStageDraw_injective v I)
      (markedDirtyFixedEdgeChoiceCode hZ source I ⟨edge.2.1,rfl⟩).2.2.2 := by
  dsimp only
  apply markedMemoryStageBirthGate_of_memo_event (2*v.val+2) _ σ hσ
  exact markedMemoryHistoryMemo_edge hZ history v

end
end ArtinMatthews
