module

public import ArtinMatthews.MarkedMemoryLifespanGhostQueue
public import ArtinMatthews.MarkedMemoryQueueOriginLabels
public import ArtinMatthews.MarkedMemoryHistoryGhostOrigins
public import ArtinMatthews.MarkedMemoryPopulationTransport
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

/-! Exact identity relabeling for the reconstructed ghost. The proof
uses the actual indexed population-origin map and the literal ordered
survivor/birth tuple. It does not infer identity from a numeric prime. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] {A : J → Type*} {P : J → Finset Nat.Primes}
  {M B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (active : MarkedRawActive P M)
  (ids : (j : J) → Fin M → A j) (queue born : (j : J) → List (A j))
  (particle : (j : J) → A j → MarkedRawParticle (P j)) (last : (j : J) → A j → ℕ) (t : ℕ)
  (hsource : (∑ j, (queue j).length) ≤ B)
  (hdeath : ∀ j i, last j ((queue j).get i) = t →
    MarkedRawParticleHits (P j) z.1 (hZ _ z.2) (particle j ((queue j).get i)))
  (htarget : (∑ j, (markedMemoryGhostQueueAfter queue born last t j).length) ≤ B)

local notation "queueSource" => (z,(active,markedMemoryLabeledQueueState queue particle hsource))
local notation "ghostChoice" => markedMemoryGhostQueueChoice hZ z active queue born particle last t hsource hdeath htarget

def markedMemoryGhostQueueSourceLabel : MarkedMemoryPopulationIndex queueSource → Σ j, A j :=
  Sum.elim (fun a => ⟨a.1,ids a.1 a.2⟩) (fun a => ⟨a.1,(queue a.1).get a.2⟩)

def markedMemoryGhostQueueBirthLabel : MarkedMemoryGhostBirthIndex ghostChoice → Σ j, A j :=
  fun a => ⟨a.1,(born a.1).get a.2⟩

def markedMemoryGhostQueueTargetLabel :
    MarkedMemoryPopulationIndex (markedMemoryGhostChoiceTarget hZ queueSource ghostChoice) → Σ j, A j :=
  Sum.elim (fun a => ⟨a.1,ids a.1 a.2⟩) (fun a => ⟨a.1,
    markedMemoryRetainedAppendTuple (queue a.1) (born a.1)
      (Finset.univ \ markedMemoryGhostQueueDeletion queue last t a.1) a.2⟩)

theorem markedMemoryGhostQueueLabel_step
    (i : MarkedMemoryPopulationIndex (markedMemoryGhostChoiceTarget hZ queueSource ghostChoice)) :
    Sum.elim (markedMemoryGhostQueueSourceLabel z active ids queue particle hsource)
      (markedMemoryGhostQueueBirthLabel hZ z active queue born particle last t hsource hdeath htarget)
      (markedMemoryGhostPopulationOrigin hZ queueSource ghostChoice i) =
        markedMemoryGhostQueueTargetLabel hZ z active ids queue born particle last t hsource hdeath htarget i := by
  rcases i with ⟨j,k⟩ | ⟨j,k⟩
  · rfl
  · rw [markedMemoryGhostPopulationOrigin_pending]
    have hcomp (o : ↥(Finset.univ \ markedMemoryGhostQueueDeletion queue last t j) ⊕ Fin (born j).length) :
        Sum.elim (markedMemoryGhostQueueSourceLabel z active ids queue particle hsource)
          (markedMemoryGhostQueueBirthLabel hZ z active queue born particle last t hsource hdeath htarget)
          (Sum.elim (fun old => Sum.inl (Sum.inr ⟨j,old.1⟩)) (fun birth => Sum.inr ⟨j,birth⟩) o) =
            (⟨j,Sum.elim (fun old => (queue j).get old.1) (born j).get o⟩ : Σ j, A j) := by
      cases o <;> rfl
    exact (hcomp (markedMemoryQueueIndexOrigin (queue j)
      (Finset.univ \ markedMemoryGhostQueueDeletion queue last t j) (born j).length k)).trans
      (congrArg (Sigma.mk j) (markedMemoryRetainedAppendTuple_origin (queue j) (born j) _ k))

theorem markedMemoryGhostQueueTargetLabel_cast
    (next : (j : J) → List (A j)) (hnext : (∑ j, (next j).length) ≤ B)
    (hqueue : markedMemoryGhostQueueAfter queue born last t = next)
    (hstate : markedMemoryGhostChoiceTarget hZ queueSource ghostChoice =
      (z,(active,markedMemoryLabeledQueueState next particle hnext)))
    (i : MarkedMemoryPopulationIndex (markedMemoryGhostChoiceTarget hZ queueSource ghostChoice)) :
    markedMemoryGhostQueueSourceLabel z active ids next particle hnext
      (markedMemoryPopulationStateCast hstate i) =
        markedMemoryGhostQueueTargetLabel hZ z active ids queue born particle last t hsource hdeath htarget i := by
  rcases i with ⟨j,k⟩ | ⟨j,k⟩
  · rw [markedMemoryPopulationStateCast_active]
    rfl
  · rw [markedMemoryPopulationStateCast_pending]
    let index : Fin (next j).length := Fin.cast
      (congrArg (fun r : MarkedRawState P M B Z => (r.2.2.1.1 j : ℕ)) hstate) k
    change (⟨j,(next j).get index⟩ : Σ j, A j) =
      ⟨j,markedMemoryRetainedAppendTuple (queue j) (born j)
        (Finset.univ \ markedMemoryGhostQueueDeletion queue last t j) k⟩
    apply congrArg (Sigma.mk j)
    have hl : List.ofFn (markedMemoryRetainedAppendTuple (queue j) (born j)
        (Finset.univ \ markedMemoryGhostQueueDeletion queue last t j)) = next j :=
      (markedMemoryRetainedAppendTuple_list _ _ _).trans (congrFun hqueue j)
    exact (markedMemoryListGet_ofFn_eq _ _ hl index).trans (congrArg _ (Fin.ext rfl))

end
end ArtinMatthews
