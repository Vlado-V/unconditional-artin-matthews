module

public import ArtinMatthews.MarkedMemoryHistoryGhostChoice
public import ArtinMatthews.MarkedMemoryIndexedQueues
public import ArtinMatthews.MarkedMemoryQueueOrder
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

/-! Construct a literal ghost choice directly from independent identity
queues and lifespan endpoints. The output raw memory realizes the same
ordered identity queue, with every newly born particle anchored here. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*} {P : J → Finset Nat.Primes}
  {M B : ℕ} {Z : Finset (ℤ × ℤ)}

def markedMemoryLabeledQueueState (queue : (j : J) → List (A j))
    (particle : (j : J) → A j → MarkedRawParticle (P j))
    (hB : (∑ j, (queue j).length) ≤ B) : MarkedRawMemory P B :=
  ⟨⟨fun j => ⟨(queue j).length,by
    have h := (Finset.single_le_sum (fun i _ => Nat.zero_le (queue i).length) (Finset.mem_univ j)).trans hB
    omega⟩,hB⟩,fun j i => particle j ((queue j).get i)⟩

theorem markedMemoryLabeledQueueState_list (queue : (j : J) → List (A j))
    (particle : (j : J) → A j → MarkedRawParticle (P j))
    (hB : (∑ j, (queue j).length) ≤ B) (j : J) :
    List.ofFn ((markedMemoryLabeledQueueState queue particle hB).2 j) = (queue j).map (particle j) := by
  change List.ofFn (fun i => particle j ((queue j).get i)) = _
  rw [List.ofFn_comp', List.ofFn_get]

def markedMemoryGhostQueueDeletion (queue : (j : J) → List (A j))
    (last : (j : J) → A j → ℕ) (t : ℕ) (j : J) : Finset (Fin (queue j).length) :=
  Finset.univ.filter (fun i => last j ((queue j).get i) = t)

def markedMemoryGhostQueueAfter (queue born : (j : J) → List (A j))
    (last : (j : J) → A j → ℕ) (t : ℕ) (j : J) : List (A j) :=
  markedMemoryRetainedQueue (queue j) (Finset.univ \ markedMemoryGhostQueueDeletion queue last t j) ++ born j

omit [Fintype J] in
theorem markedMemoryGhostQueueAfter_eq (queue born : (j : J) → List (A j))
    (last : (j : J) → A j → ℕ) (t : ℕ)
    (halive : ∀ j i, t ≤ last j ((queue j).get i)) (j : J) :
    markedMemoryGhostQueueAfter queue born last t j = markedMemoryGhostQueue (queue j) (born j) (last j) t := by
  have hs : Finset.univ \ markedMemoryGhostQueueDeletion queue last t j =
      Finset.univ.filter (fun i => t < last j ((queue j).get i)) := by
    ext i
    simp only [markedMemoryGhostQueueDeletion, Finset.mem_sdiff, Finset.mem_univ,
      Finset.mem_filter, true_and]
    have := halive j i
    omega
  unfold markedMemoryGhostQueueAfter markedMemoryGhostQueue
  rw [hs]
  exact congrArg (fun l => l ++ born j)
    (markedMemoryRetainedQueue_filter_eq (queue j) (fun a => t < last j a))

def markedMemoryGhostQueueChoice (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z)
    (active : MarkedRawActive P M) (queue born : (j : J) → List (A j))
    (particle : (j : J) → A j → MarkedRawParticle (P j)) (last : (j : J) → A j → ℕ) (t : ℕ)
    (hsource : (∑ j, (queue j).length) ≤ B)
    (hdeath : ∀ j i, last j ((queue j).get i) = t →
      MarkedRawParticleHits (P j) z.1 (hZ _ z.2) (particle j ((queue j).get i)))
    (htarget : (∑ j, (markedMemoryGhostQueueAfter queue born last t j).length) ≤ B) :
    MarkedMemoryGhostChoice hZ (z,(active,markedMemoryLabeledQueueState queue particle hsource)) where
  deletion := markedMemoryGhostQueueDeletion queue last t
  allowed := by
    intro j i hi
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,hdeath j i (Finset.mem_filter.mp hi).2⟩
  sizes := ⟨fun j => ⟨(born j).length,by
      have h := (Finset.single_le_sum (fun i _ => Nat.zero_le
        (markedMemoryGhostQueueAfter queue born last t i).length) (Finset.mem_univ j)).trans htarget
      simp only [markedMemoryGhostQueueAfter, List.length_append, markedMemoryRetainedQueue_length] at h
      omega⟩,by
        change (∑ j, ((Finset.univ \ markedMemoryGhostQueueDeletion queue last t j).card + (born j).length)) ≤ B
        simpa only [markedMemoryGhostQueueAfter, List.length_append, markedMemoryRetainedQueue_length] using htarget⟩
  births := fun j k => (particle j ((born j).get k)).1

theorem markedMemoryGhostQueueChoice_target (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z)
    (active : MarkedRawActive P M) (queue born : (j : J) → List (A j))
    (particle : (j : J) → A j → MarkedRawParticle (P j)) (last : (j : J) → A j → ℕ) (t : ℕ)
    (hsource : (∑ j, (queue j).length) ≤ B)
    (hdeath : ∀ j i, last j ((queue j).get i) = t →
      MarkedRawParticleHits (P j) z.1 (hZ _ z.2) (particle j ((queue j).get i)))
    (htarget : (∑ j, (markedMemoryGhostQueueAfter queue born last t j).length) ≤ B)
    (hborn : ∀ j a, a ∈ born j → particle j a = markedRawAnchoredParticle (P j) (particle j a).1 z.1 (hZ _ z.2)) :
    markedMemoryGhostChoiceTarget hZ _ (markedMemoryGhostQueueChoice hZ z active queue born particle last t hsource hdeath htarget) =
      (z,(active,markedMemoryLabeledQueueState (markedMemoryGhostQueueAfter queue born last t) particle htarget)) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · rfl
  apply markedMemoryState_eq_of_lists
  intro j
  rw [markedMemoryLabeledQueueState_list]
  change List.ofFn ((markedRawGhostTargetMemory _ _ _ _ _ _).2 j) = _
  rw [markedMemoryGhostTargetMemory_list]
  change List.ofFn (fun k => particle j ((queue j).get
      ((Finset.univ \ markedMemoryGhostQueueDeletion queue last t j).orderEmbOfFin rfl k))) ++
      List.ofFn (fun k : Fin (born j).length => markedRawAnchoredParticle (P j)
        (particle j ((born j).get k)).1 z.1 (hZ _ z.2)) = _
  rw [markedMemoryGhostQueueAfter, List.map_append]
  apply congrArg₂ (fun x y => x ++ y)
  · simp only [markedMemoryRetainedQueue, List.map_ofFn]
    rfl
  · calc
      _ = List.ofFn (fun k : Fin (born j).length => particle j ((born j).get k)) := by
        congr 1
        funext k
        exact (hborn j _ (List.get_mem _ _)).symm
      _ = (born j).map (particle j) := by
        rw [List.ofFn_comp', List.ofFn_get]

end
end ArtinMatthews
