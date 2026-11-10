module

public import ArtinMatthews.MarkedMemoryRunReconstruction
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

/-! Direct target-state formulas for independent local run data. These
formulas use retained old lists, newly born labels, old/fresh target origins
and source-last stores; they contain no chronological-history argument. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {M pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

def markedMemoryGhostRunTargetSizes (s : MarkedRawState P M B Z)
    (d : MarkedMemoryGhostRunData hZ s) : MarkedRawMemorySizes J B :=
  markedRawGhostTargetSizes s.2.2 (markedMemoryGhostRunDeletion hZ s d)
    (markedMemoryGhostRunBirthSizes hZ s d)

/-- The complement-of-deaths survivor set is exactly the retained set by
`markedMemoryGhostRun_survivors`; new labels follow in their given order. -/
def markedMemoryGhostRunTarget (s : MarkedRawState P M B Z)
    (d : MarkedMemoryGhostRunData hZ s) : MarkedRawState P M B Z :=
  (s.1,(s.2.1,⟨markedMemoryGhostRunTargetSizes hZ s d,fun j => Fin.addCases
    (fun k => s.2.2.2 j ((markedRawGhostSurvivors s.2.2
      (markedMemoryGhostRunDeletion hZ s d) j).orderEmbOfFin rfl k))
    (fun k => markedRawAnchoredParticle (P j) ((d.born j).get k) s.1.1 (hZ _ s.1.2))⟩))

theorem markedMemoryGhostRunReconstruct_target (s : MarkedRawState P M B Z)
    (d : MarkedMemoryGhostRunData hZ s) :
    markedMemoryGhostChoiceTarget hZ s (markedMemoryGhostRunReconstruct hZ s d) =
      markedMemoryGhostRunTarget hZ s d := rfl

def markedMemoryEdgeRunStoreSizes (s : MarkedRawState P (pads+1) B Z)
    (d : MarkedMemoryEdgeRunData hZ s) :
    MarkedRawGhostBirthSizes s.2.2 (markedRawEdgePromotionDeletion (markedMemoryRunPromotion s d.targetLastOrigin)) :=
  ⟨fun j => ⟨if d.sourceLastSurvives j then 1 else 0,by
    have h := (Finset.single_le_sum (fun i _ => Nat.zero_le
      ((markedRawGhostSurvivors s.2.2
        (markedRawEdgePromotionDeletion (markedMemoryRunPromotion s d.targetLastOrigin)) i).card +
        (if d.sourceLastSurvives i then 1 else 0))) (Finset.mem_univ j)).trans d.memory_bound
    omega⟩,d.memory_bound⟩

/-- Old promotion is removed before the optional old source-last store;
the new active label is obtained from its actual old-or-fresh origin. -/
def markedMemoryEdgeRunTarget (s : MarkedRawState P (pads+1) B Z)
    (d : MarkedMemoryEdgeRunData hZ s) : MarkedRawState P (pads+1) B Z :=
  (d.target,((markedRawActiveSplit pads).symm
    (((markedRawActiveSplit pads) s.2.1).1,markedMemoryRunLastPrime s d.targetLastOrigin),
      markedRawGhostTargetMemory s.2.2 s.1.1 (hZ _ s.1.2)
        (markedRawEdgePromotionDeletion (markedMemoryRunPromotion s d.targetLastOrigin))
        (markedMemoryEdgeRunStoreSizes hZ s d) (fun j _ => ((markedRawActiveSplit pads) s.2.1).2 j)))

theorem markedMemoryEdgeRunReconstruct_target (s : MarkedRawState P (pads+1) B Z)
    (d : MarkedMemoryEdgeRunData hZ s) :
    markedRawEdgeTargetState hZ s (markedMemoryEdgeRunReconstruct hZ s d) =
      markedMemoryEdgeRunTarget hZ s d := by
  unfold markedRawEdgeTargetState
  rw [markedMemoryEdgeRunReconstruct_last]
  rfl

theorem markedMemorySlotEdgeRunTarget_eq (s : MarkedRawState P (pads+1) B Z)
    (d : MarkedMemorySlotEdgeRunData hZ s) :
    markedMemorySlotEdgeRunTarget hZ s d =
      markedRawSlotEquiv d.2.2 (markedMemoryEdgeRunTarget hZ (markedRawSlotEquiv d.1 s) d.2.1) := by
  unfold markedMemorySlotEdgeRunTarget markedMemoryEdgeChoiceTarget
  exact congrArg (markedRawSlotEquiv d.2.2)
    (markedMemoryEdgeRunReconstruct_target hZ (markedRawSlotEquiv d.1 s) d.2.1)

end
end ArtinMatthews
