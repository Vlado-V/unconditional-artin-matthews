module

public import ArtinMatthews.MarkedMemoryIndependentGhostLabels
public import ArtinMatthews.MarkedMemoryIndependentEdgeLabels
public import ArtinMatthews.MarkedMemoryHistoryEdgeSlotOrigins
public import ArtinMatthews.MarkedMemorySlotOriginLabels
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

/-! The independent labels follow the literal slotted edge origin. The
canonical target comparison uses the proved active matching and ordered
queue equality, so no label compatibility or bijection is assumed. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {n : ℕ}
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (v : ℕ) (hv : v < n) (order : J → Equiv.Perm (Fin pads))

local notation "src" => markedMemoryIndependentPostGhost hZ d v (Nat.le_of_lt hv)
local notation "σ" => markedMemoryIndependentSourceSlots hZ d v hv order
local notation "τ" => markedMemoryIndependentTargetSlots hZ d v hv order
local notation "raw" => markedMemoryIndependentRawEdge hZ d v hv order
local notation "edge" => markedMemoryIndependentEdge hZ d v hv order
local notation "dst" => markedMemoryIndependentState hZ d (v+1) hv
local notation "nextQueue" => markedMemoryIndependentQueue hZ d (2*(v+1))

theorem markedMemoryIndependentRawEdgeLabel_cast
    (i : MarkedMemoryPopulationIndex (markedRawEdgeTargetState hZ (markedRawSlotEquiv σ src) raw)) :
    markedMemoryEdgeSourceLabel (markedRawSlotEquiv (fun j => (τ j).symm) dst)
      (fun j k => d.activeId (v+1) j ((τ j).symm k)) (fun j => (nextQueue j).get)
      (markedMemoryPopulationStateCast (markedMemoryIndependentRawEdge_target hZ d v hv order) i) =
      markedMemoryEdgeTargetLabel hZ (markedRawSlotEquiv σ src) raw
        (fun j k => d.activeId v j (σ j k))
        (fun j => (markedMemoryIndependentQueue hZ d (2*v+1) j).get)
        (fun j => (d.lifespan j).incoming (2*v+1)) i :=
  markedMemoryEdgeTargetLabel_cast hZ (markedRawSlotEquiv σ src) raw
    (fun j k => d.activeId v j (σ j k))
    (fun j => (markedMemoryIndependentQueue hZ d (2*v+1) j).get)
    (fun j => (d.lifespan j).incoming (2*v+1))
    (d.position (v+1)) ((markedRawSlotEquiv (fun j => (τ j).symm) dst).2.1)
    (fun j k => d.activeId (v+1) j ((τ j).symm k)) nextQueue d.particle
    (markedMemoryIndependentQueue_bound hZ d (2*(v+1)) (by omega))
    (markedMemoryIndependentRawGroupLabel_active hZ d v hv order)
    (markedMemoryIndependentRawGroupLabel_pending hZ d v hv order)
    (markedMemoryIndependentRawEdge_target hZ d v hv order) i

theorem markedMemoryIndependentEdgeLabel_target
    (i : MarkedMemoryPopulationIndex (markedMemoryEdgeChoiceTarget hZ src edge)) :
    markedMemoryEdgeSourceLabel (markedRawSlotEquiv (fun j => (τ j).symm) dst)
      (fun j k => d.activeId (v+1) j ((τ j).symm k)) (fun j => (nextQueue j).get)
      (markedMemoryPopulationStateCast (markedMemoryIndependentRawEdge_target hZ d v hv order)
        (markedMemorySlotPopulationEquiv τ (markedRawEdgeTargetState hZ (markedRawSlotEquiv σ src) raw) i)) =
      markedMemoryIndependentVertexValue hZ d (v+1) hv
        (markedMemoryPopulationStateCast (markedMemoryIndependentEdge_target hZ d v hv order) i) := by
  let F := markedMemoryEdgeSourceLabel (markedRawSlotEquiv (fun j => (τ j).symm) dst)
    (fun j k => d.activeId (v+1) j ((τ j).symm k)) (fun j => (nextQueue j).get)
  let G := markedMemoryIndependentVertexValue hZ d (v+1) hv
  rcases i with ⟨j,k⟩ | ⟨j,k⟩
  · have hs := markedMemorySlotPopulationEquiv_active τ (markedRawEdgeTargetState hZ (markedRawSlotEquiv σ src) raw) j k
    have hr := markedMemoryPopulationStateCast_active (markedMemoryIndependentRawEdge_target hZ d v hv order) j (τ j k)
    have hf := markedMemoryPopulationStateCast_active (markedMemoryIndependentEdge_target hZ d v hv order) j k
    refine (congrArg F ((congrArg (markedMemoryPopulationStateCast (markedMemoryIndependentRawEdge_target hZ d v hv order)) hs).trans hr)).trans ?_
    refine Eq.trans ?_ (congrArg G hf.symm)
    change (⟨j,d.activeId (v+1) j ((τ j).symm (τ j k))⟩ : Σ j, A j) = ⟨j,d.activeId (v+1) j k⟩
    rw [Equiv.symm_apply_apply]
  · let kr : Fin (nextQueue j).length := Fin.cast
      (congrArg (fun r : MarkedRawState P (pads+1) B Z => (r.2.2.1.1 j : ℕ))
        (markedMemoryIndependentRawEdge_target hZ d v hv order)) k
    let kf : Fin (nextQueue j).length := Fin.cast
      (congrArg (fun r : MarkedRawState P (pads+1) B Z => (r.2.2.1.1 j : ℕ))
        (markedMemoryIndependentEdge_target hZ d v hv order)) k
    have hs := markedMemorySlotPopulationEquiv_pending τ (markedRawEdgeTargetState hZ (markedRawSlotEquiv σ src) raw) j k
    have hr := markedMemoryPopulationStateCast_pending (markedMemoryIndependentRawEdge_target hZ d v hv order) j k
    have hf := markedMemoryPopulationStateCast_pending (markedMemoryIndependentEdge_target hZ d v hv order) j k
    refine (congrArg F ((congrArg (markedMemoryPopulationStateCast (markedMemoryIndependentRawEdge_target hZ d v hv order)) hs).trans hr)).trans ?_
    refine Eq.trans ?_ (congrArg G hf.symm)
    exact congrArg (fun k : Fin (nextQueue j).length => (⟨j,(nextQueue j).get k⟩ : Σ j, A j)) (show kr = kf from Fin.ext rfl)

theorem markedMemoryIndependentEdge_label_step
    (i : MarkedMemoryPopulationIndex (markedMemoryEdgeChoiceTarget hZ src edge)) :
    Sum.elim (markedMemoryIndependentPostGhostValue hZ d v (Nat.le_of_lt hv))
      (markedMemoryIndependentEdgeBirthLabel hZ d v hv order)
      (markedMemoryEdgeSlotPopulationOrigin hZ src edge i) =
      markedMemoryIndependentVertexValue hZ d (v+1) hv
        (markedMemoryPopulationStateCast (markedMemoryIndependentEdge_target hZ d v hv order) i) := by
  have hprom : ∀ j k, (raw).promotions j = some k →
      (markedMemoryIndependentQueue hZ d (2*v+1) j).get k = (d.lifespan j).incoming (2*v+1) := by
    intro j k hk
    exact (markedMemoryEdgeQueuePromotion_eq_some (markedMemoryIndependentQueue hZ d (2*v+1))
      (markedMemoryIndependentQueue_nodup hZ d (2*v+1) (by omega))
      (fun j => (d.lifespan j).incoming (2*v+1)) j k).mp hk
  have h := markedMemoryEdgeSlotPopulationOrigin_label hZ src edge (fun j k => d.activeId v j k)
    (fun j => (markedMemoryIndependentQueue hZ d (2*v+1) j).get)
    (fun j => (d.lifespan j).incoming (2*v+1)) hprom i
  exact h.trans ((markedMemoryIndependentRawEdgeLabel_cast hZ d v hv order _).symm.trans
    (markedMemoryIndependentEdgeLabel_target hZ d v hv order i))

end
end ArtinMatthews
