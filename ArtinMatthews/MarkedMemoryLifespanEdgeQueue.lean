module

public import ArtinMatthews.MarkedMemoryLifespanGhostQueue
public import ArtinMatthews.MarkedMemoryLifespanEdgeReconstruction
public import ArtinMatthews.MarkedMemoryQueueOrder
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
public import Mathlib.Tactic.Basify
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

/-! Reconstruct actual old-only promotions from independent pending
identity queues. Removing the incoming identity precedes any new store,
and repeated numeric prime values do not affect identity lookup. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

def markedMemoryQueueEmbedding {A : Type*} (queue : List A) (hqueue : queue.Nodup) : Fin queue.length ↪ A :=
  ⟨queue.get,hqueue.injective_get⟩

variable {J : Type*} [Fintype J] {A : J → Type*} [∀ j, DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}

def markedMemoryEdgeQueuePromotion (queue : (j : J) → List (A j)) (hq : ∀ j, (queue j).Nodup)
    (incoming : (j : J) → A j) (j : J) : Option (Fin (queue j).length) :=
  markedMemoryLifespanOldIndex (markedMemoryQueueEmbedding (queue j) (hq j)) (incoming j)

omit [Fintype J] [∀ j, DecidableEq (A j)] in
theorem markedMemoryEdgeQueuePromotion_eq_some (queue : (j : J) → List (A j)) (hq : ∀ j, (queue j).Nodup)
    (incoming : (j : J) → A j) (j : J) (k : Fin (queue j).length) :
    markedMemoryEdgeQueuePromotion queue hq incoming j = some k ↔ (queue j).get k = incoming j :=
  markedMemoryLifespanOldIndex_eq_some _ _ _

def markedMemoryEdgeQueueAfter (queue : (j : J) → List (A j)) (hq : ∀ j, (queue j).Nodup)
    (incoming outgoing : (j : J) → A j) (store : J → Bool) (j : J) : List (A j) :=
  markedMemoryRetainedQueue (queue j) (Finset.univ \ (markedMemoryEdgeQueuePromotion queue hq incoming j).toFinset) ++
    if store j then [outgoing j] else []

omit [Fintype J] in
theorem markedMemoryEdgeQueueAfter_eq (queue : (j : J) → List (A j)) (hq : ∀ j, (queue j).Nodup)
    (incoming outgoing : (j : J) → A j) (store : J → Bool) (j : J) :
    markedMemoryEdgeQueueAfter queue hq incoming outgoing store j =
      markedMemoryEdgeQueue (queue j) (incoming j) (outgoing j) (store j) := by
  have hs : Finset.univ \ (markedMemoryEdgeQueuePromotion queue hq incoming j).toFinset =
      Finset.univ.filter (fun k => (queue j).get k ≠ incoming j) := by
    ext k
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Option.mem_toFinset,
      Option.mem_def, markedMemoryEdgeQueuePromotion_eq_some, Finset.mem_filter]
  unfold markedMemoryEdgeQueueAfter markedMemoryEdgeQueue
  rw [hs]
  exact congrArg (fun l => l ++ if store j then [outgoing j] else [])
    (markedMemoryRetainedQueue_filter_eq (queue j) (fun a => a ≠ incoming j))

omit [Fintype J] [∀ j, DecidableEq (A j)] in
theorem markedMemoryEdgeQueueAfter_length (queue : (j : J) → List (A j)) (hq : ∀ j, (queue j).Nodup)
    (incoming outgoing : (j : J) → A j) (store : J → Bool) (j : J) :
    (markedMemoryEdgeQueueAfter queue hq incoming outgoing store j).length =
      (Finset.univ \ (markedMemoryEdgeQueuePromotion queue hq incoming j).toFinset).card +
        (if store j then 1 else 0) := by
  unfold markedMemoryEdgeQueueAfter
  rw [List.length_append, markedMemoryRetainedQueue_length]
  cases store j <;> rfl

def markedMemoryEdgeQueueChoice (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z target : Z)
    (active : MarkedRawActive P (pads+1)) (queue : (j : J) → List (A j)) (hq : ∀ j, (queue j).Nodup)
    (incoming outgoing : (j : J) → A j) (store : J → Bool)
    (particle : (j : J) → A j → MarkedRawParticle (P j))
    (hsource : (∑ j, (queue j).length) ≤ B)
    (hhit : ∀ j k, (queue j).get k = incoming j →
      MarkedRawParticleHits (P j) target.1 (hZ _ target.2) (particle j ((queue j).get k)))
    (htarget : (∑ j, (markedMemoryEdgeQueueAfter queue hq incoming outgoing store j).length) ≤ B) :
    MarkedRawEdgeChoice hZ (z,(active,markedMemoryLabeledQueueState queue particle hsource)) where
  target := target
  store := store
  promotions := markedMemoryEdgeQueuePromotion queue hq incoming
  fresh := (markedRawEdgeDegreeLabelsEquiv (markedMemoryLabeledQueueState queue particle hsource)
    (markedMemoryEdgeQueuePromotion queue hq incoming)).symm
    ⟨fun j => (particle j (incoming j)).1,by
      intro j k hk
      have hi := (markedMemoryEdgeQueuePromotion_eq_some queue hq incoming j k).mp hk
      change (particle j (incoming j)).1 = (particle j ((queue j).get k)).1
      rw [hi]⟩
  promotion_hits := by
    intro j k hk
    exact hhit j k ((markedMemoryEdgeQueuePromotion_eq_some queue hq incoming j k).mp hk)
  memory_bound := by
    change (∑ j, ((Finset.univ \ (markedMemoryEdgeQueuePromotion queue hq incoming j).toFinset).card +
      (if store j then 1 else 0))) ≤ B
    simpa only [markedMemoryEdgeQueueAfter_length] using htarget

omit [∀ j, DecidableEq (A j)] in
theorem markedMemoryEdgeQueueChoice_target_prime (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z target : Z)
    (active : MarkedRawActive P (pads+1)) (queue : (j : J) → List (A j)) (hq : ∀ j, (queue j).Nodup)
    (incoming outgoing : (j : J) → A j) (store : J → Bool)
    (particle : (j : J) → A j → MarkedRawParticle (P j))
    (hsource : (∑ j, (queue j).length) ≤ B)
    (hhit : ∀ j k, (queue j).get k = incoming j →
      MarkedRawParticleHits (P j) target.1 (hZ _ target.2) (particle j ((queue j).get k)))
    (htarget : (∑ j, (markedMemoryEdgeQueueAfter queue hq incoming outgoing store j).length) ≤ B) :
    markedRawEdgeTargetLast (markedMemoryLabeledQueueState queue particle hsource)
      (markedMemoryEdgeQueueChoice hZ z target active queue hq incoming outgoing store particle hsource hhit htarget).promotions
      (markedMemoryEdgeQueueChoice hZ z target active queue hq incoming outgoing store particle hsource hhit htarget).fresh =
      fun j => (particle j (incoming j)).1 := by
  rw [← markedRawEdgeDegreeLabelsEquiv_value]
  exact congrArg Subtype.val ((markedRawEdgeDegreeLabelsEquiv (markedMemoryLabeledQueueState queue particle hsource)
    (markedMemoryEdgeQueuePromotion queue hq incoming)).apply_symm_apply _)

end
end ArtinMatthews
