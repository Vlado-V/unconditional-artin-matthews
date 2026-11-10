module

public import ArtinMatthews.MarkedMemoryLifespanGhostQueue
public import ArtinMatthews.MarkedMemoryPhysicalSlotQuotient
public import ArtinMatthews.MarkedMemoryLifespanQueueSchedule
public import ArtinMatthews.MarkedMemoryLifespanQueueMemory
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
public import Mathlib.RingTheory.WittVector.IsPoly
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

/-! Independent finite lifespan data with active-slot identities and
physical labels. Pending queues and local choices are not fields: they
are reconstructed from the intervals and active incidences. Birth lists
retain their order. Admissibility states the literal hit/anchor rules. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}

structure MarkedMemoryIndependentLifespans
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (n : ℕ) where
  lifespan : (j : J) → MarkedMemoryQueueLifespanData (A j) (2*n+1)
  position : ℕ → Z
  activeId : ℕ → (j : J) → Fin (pads+1) ↪ A j
  particle : (j : J) → A j → MarkedRawParticle (P j)
  active_mem : ∀ v, v ≤ n → ∀ j a,
    (lifespan j).active (2*v) a ↔ ∃ i, activeId v j i = a
  active_alive : ∀ v, v ≤ n → ∀ j i,
    (lifespan j).first (activeId v j i) ≤ 2*v ∧ 2*v+1 ≤ (lifespan j).last (activeId v j i)
  cutoff : ∀ t, t ≤ 2*n+1 → (∑ j, (markedMemoryPendingIdentitySet (lifespan j) t).card) ≤ B
  ghost_death_hit : ∀ v, v ≤ n → ∀ j a,
    (lifespan j).first a ≤ 2*v → (lifespan j).last a = 2*v → ¬ (lifespan j).active (2*v) a →
      MarkedRawParticleHits (P j) (position v).1 (hZ _ (position v).2) (particle j a)
  ghost_birth_anchor : ∀ v, v ≤ n → ∀ j a, a ∈ (lifespan j).births (2*v) →
    particle j a = markedRawAnchoredParticle (P j) (particle j a).1 (position v).1 (hZ _ (position v).2)
  promotion_hit : ∀ v, v < n → ∀ j,
    (lifespan j).first ((lifespan j).incoming (2*v+1)) ≤ 2*v+1 →
    2*v+1 ≤ (lifespan j).last ((lifespan j).incoming (2*v+1)) →
    ¬ (lifespan j).active (2*v+1) ((lifespan j).incoming (2*v+1)) →
      MarkedRawParticleHits (P j) (position (v+1)).1 (hZ _ (position (v+1)).2)
        (particle j ((lifespan j).incoming (2*v+1)))
  store_anchor : ∀ v, v < n → ∀ j,
    2*v+1 < (lifespan j).last ((lifespan j).outgoing (2*v+1)) →
      particle j ((lifespan j).outgoing (2*v+1)) =
        markedRawAnchoredParticle (P j) (particle j ((lifespan j).outgoing (2*v+1))).1
          (position v).1 (hZ _ (position v).2)

variable (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {n : ℕ}
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

def markedMemoryIndependentQueue (t : ℕ) (j : J) : List (A j) :=
  markedMemoryPendingQueueAt (d.lifespan j) t

theorem markedMemoryIndependentQueue_bound (t : ℕ) (ht : t ≤ 2*n+1) :
    (∑ j, (markedMemoryIndependentQueue hZ d t j).length) ≤ B :=
  markedMemoryGroupedPendingQueue_bound d.lifespan t ht (d.cutoff t ht)

def markedMemoryIndependentMemory (t : ℕ) (ht : t ≤ 2*n+1) : MarkedRawMemory P B :=
  markedMemoryLabeledQueueState (markedMemoryIndependentQueue hZ d t) d.particle
    (markedMemoryIndependentQueue_bound hZ d t ht)

def markedMemoryIndependentState (v : ℕ) (hv : v ≤ n) : MarkedRawState P (pads+1) B Z :=
  markedMemoryIdentityRawState (fun j a => (d.particle j a).1) (d.activeId v) (d.position v)
    (markedMemoryIndependentMemory hZ d (2*v) (by omega))

def markedMemoryIndependentPostGhost (v : ℕ) (hv : v ≤ n) : MarkedRawState P (pads+1) B Z :=
  markedMemoryIdentityRawState (fun j a => (d.particle j a).1) (d.activeId v) (d.position v)
    (markedMemoryIndependentMemory hZ d (2*v+1) (by omega))

theorem markedMemoryIndependentQueue_ghost (v : ℕ) (hv : v ≤ n) :
    markedMemoryGhostQueueAfter (markedMemoryIndependentQueue hZ d (2*v))
      (fun j => (d.lifespan j).births (2*v)) (fun j => (d.lifespan j).last) (2*v) =
      markedMemoryIndependentQueue hZ d (2*v+1) := by
  funext j
  calc
    _ = markedMemoryGhostQueue (markedMemoryIndependentQueue hZ d (2*v) j)
        ((d.lifespan j).births (2*v)) (d.lifespan j).last (2*v) :=
      markedMemoryGhostQueueAfter_eq (markedMemoryIndependentQueue hZ d (2*v))
        (fun j => (d.lifespan j).births (2*v)) (fun j => (d.lifespan j).last) (2*v)
        (fun j i => ((markedMemoryPendingQueueAt_mem (d.lifespan j) (2*v) (by omega) _).mp (List.get_mem _ i)).2.1) j
    _ = _ := by
      change _ = markedMemoryPendingQueueAt (d.lifespan j) (2*v+1)
      have he : (2*v) % 2 = 0 := by omega
      simp only [markedMemoryPendingQueueAt, he, ite_true]
      rfl

def markedMemoryIndependentGhost (v : ℕ) (hv : v ≤ n) :
    MarkedMemoryGhostChoice hZ (markedMemoryIndependentState hZ d v hv) :=
  markedMemoryGhostQueueChoice hZ (d.position v) (fun j k => (d.particle j (d.activeId v j k)).1)
    (markedMemoryIndependentQueue hZ d (2*v)) (fun j => (d.lifespan j).births (2*v))
    d.particle (fun j => (d.lifespan j).last) (2*v)
    (markedMemoryIndependentQueue_bound hZ d (2*v) (by omega))
    (by
      intro j i hi
      have hm := (markedMemoryPendingQueueAt_mem (d.lifespan j) (2*v) (by omega) _).mp (List.get_mem _ i)
      exact d.ghost_death_hit v hv j _ hm.1 hi hm.2.2)
    (by
      rw [markedMemoryIndependentQueue_ghost hZ d v hv]
      exact markedMemoryIndependentQueue_bound hZ d (2*v+1) (by omega))

/-- Every reconstructed ghost has exactly the independently computed
post-ghost queue, at the original position and active tuple. -/
theorem markedMemoryIndependentGhost_target (v : ℕ) (hv : v ≤ n) :
    markedMemoryGhostChoiceTarget hZ (markedMemoryIndependentState hZ d v hv)
      (markedMemoryIndependentGhost hZ d v hv) = markedMemoryIndependentPostGhost hZ d v hv := by
  dsimp only [markedMemoryIndependentGhost, markedMemoryIndependentState,
    markedMemoryIndependentPostGhost, markedMemoryIdentityRawState, markedMemoryIndependentMemory]
  rw [markedMemoryGhostQueueChoice_target _ _ _ _ _ _ _ _ _ _ _ (d.ghost_birth_anchor v hv)]
  apply Prod.ext
  · rfl
  apply Prod.ext
  · rfl
  apply markedMemoryState_eq_of_lists
  intro j
  rw [markedMemoryLabeledQueueState_list, markedMemoryLabeledQueueState_list,
    markedMemoryIndependentQueue_ghost hZ d v hv]

end
end ArtinMatthews
