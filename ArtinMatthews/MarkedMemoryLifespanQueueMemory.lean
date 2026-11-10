module

public import ArtinMatthews.MarkedMemoryLifespanQueueSchedule
public import ArtinMatthews.MarkedMemoryQueueState
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

/-! Turn independent per-band lifespan queues into the actual total-
truncated raw memory. The cutoff is the sum over all bands, and equal
numeric particle values are retained as separate ordered entries. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)]
  {P : J → Finset Nat.Primes} {H B : ℕ}

theorem markedMemoryGroupedPendingQueue_length
    (d : (j : J) → MarkedMemoryQueueLifespanData (A j) H) (t : ℕ) (ht : t ≤ H) :
    (∑ j, (markedMemoryPendingQueueAt (d j) t).length) =
      ∑ j, (markedMemoryPendingIdentitySet (d j) t).card := by
  apply Finset.sum_congr rfl
  intro j _
  exact markedMemoryPendingQueueAt_length (d j) t ht

theorem markedMemoryGroupedPendingQueue_bound
    (d : (j : J) → MarkedMemoryQueueLifespanData (A j) H) (t : ℕ) (ht : t ≤ H)
    (hB : (∑ j, (markedMemoryPendingIdentitySet (d j) t).card) ≤ B) :
    (∑ j, (markedMemoryPendingQueueAt (d j) t).length) ≤ B := by
  rwa [markedMemoryGroupedPendingQueue_length d t ht]

def markedMemoryLifespanQueueMemory
    (d : (j : J) → MarkedMemoryQueueLifespanData (A j) H)
    (particle : (j : J) → A j → MarkedRawParticle (P j)) (t : ℕ) (ht : t ≤ H)
    (hB : (∑ j, (markedMemoryPendingIdentitySet (d j) t).card) ≤ B) : MarkedRawMemory P B :=
  markedMemoryQueueState (fun j => (markedMemoryPendingQueueAt (d j) t).map (particle j))
    (by simpa only [List.length_map] using markedMemoryGroupedPendingQueue_bound d t ht hB)

theorem markedMemoryLifespanQueueMemory_list
    (d : (j : J) → MarkedMemoryQueueLifespanData (A j) H)
    (particle : (j : J) → A j → MarkedRawParticle (P j)) (t : ℕ) (ht : t ≤ H)
    (hB : (∑ j, (markedMemoryPendingIdentitySet (d j) t).card) ≤ B) (j : J) :
    List.ofFn ((markedMemoryLifespanQueueMemory d particle t ht hB).2 j) =
      (markedMemoryPendingQueueAt (d j) t).map (particle j) :=
  markedMemoryQueueState_list _ _ j

theorem markedMemoryLifespanQueueMemory_size
    (d : (j : J) → MarkedMemoryQueueLifespanData (A j) H)
    (particle : (j : J) → A j → MarkedRawParticle (P j)) (t : ℕ) (ht : t ≤ H)
    (hB : (∑ j, (markedMemoryPendingIdentitySet (d j) t).card) ≤ B) (j : J) :
    ((markedMemoryLifespanQueueMemory d particle t ht hB).1.1 j : ℕ) =
      (markedMemoryPendingIdentitySet (d j) t).card := by
  change ((markedMemoryPendingQueueAt (d j) t).map (particle j)).length = _
  rw [List.length_map, markedMemoryPendingQueueAt_length (d j) t ht]

end
end ArtinMatthews
