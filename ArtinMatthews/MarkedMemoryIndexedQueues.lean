module

public import ArtinMatthews.MarkedMemoryLifespanQueues
public import ArtinMatthews.MarkedMinorArcRawGhostState
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

/-! Canonical indexed survivor queues use the exact increasing old-index
order of the raw memory updater. Their incidence and uniqueness follow
from the independent lifespan queue rules. -/
namespace ArtinMatthews
noncomputable section

variable {A : Type*}

def markedMemoryRetainedQueue (queue : List A) (keep : Finset (Fin queue.length)) : List A :=
  List.ofFn (fun i => queue.get ((keep.orderIsoOfFin rfl i).1))

theorem markedMemoryRetainedQueue_mem (queue : List A) (keep : Finset (Fin queue.length)) (a : A) :
    a ∈ markedMemoryRetainedQueue queue keep ↔ ∃ i ∈ keep, queue.get i = a := by
  rw [markedMemoryRetainedQueue, List.mem_ofFn]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨_,(keep.orderIsoOfFin rfl i).2,hi⟩
  · rintro ⟨i,hi,hia⟩
    refine ⟨(keep.orderIsoOfFin rfl).symm ⟨i,hi⟩,?_⟩
    simpa only [OrderIso.apply_symm_apply] using hia

theorem markedMemoryRetainedQueue_nodup (queue : List A) (keep : Finset (Fin queue.length))
    (hq : queue.Nodup) : (markedMemoryRetainedQueue queue keep).Nodup := by
  apply List.nodup_ofFn_ofInjective
  intro i j hij
  apply (keep.orderIsoOfFin rfl).injective
  apply Subtype.ext
  exact hq.injective_get hij

@[simp] theorem markedMemoryRetainedQueue_length (queue : List A) (keep : Finset (Fin queue.length)) :
    (markedMemoryRetainedQueue queue keep).length = keep.card := List.length_ofFn

theorem markedMemoryRetainedQueue_filter_mem (queue : List A) (p : A → Prop) [DecidablePred p] (a : A) :
    a ∈ markedMemoryRetainedQueue queue (Finset.univ.filter (fun i => p (queue.get i))) ↔ a ∈ queue ∧ p a := by
  rw [markedMemoryRetainedQueue_mem]
  constructor
  · rintro ⟨i,hi,rfl⟩
    exact ⟨List.get_mem _ _,(Finset.mem_filter.mp hi).2⟩
  · rintro ⟨ha,hp⟩
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp ha
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi.symm ▸ hp⟩,hi⟩

def markedMemoryIndexedGhostQueue (queue born : List A) (last : A → ℕ) (t : ℕ) : List A :=
  markedMemoryRetainedQueue queue (Finset.univ.filter (fun i => t < last (queue.get i))) ++ born

theorem markedMemoryIndexedGhostQueue_mem (queue born : List A) (last : A → ℕ) (t : ℕ) (a : A) :
    a ∈ markedMemoryIndexedGhostQueue queue born last t ↔ a ∈ markedMemoryGhostQueue queue born last t := by
  rw [markedMemoryGhostQueue_mem]
  unfold markedMemoryIndexedGhostQueue
  rw [List.mem_append]
  exact or_congr (markedMemoryRetainedQueue_filter_mem queue (fun a => t < last a) a) Iff.rfl

theorem markedMemoryIndexedGhostQueue_nodup (queue born : List A) (first last : A → ℕ) (t : ℕ)
    (hq : queue.Nodup) (hb : born.Nodup)
    (hfirst : ∀ a ∈ queue, first a ≤ t) (hborn : ∀ a ∈ born, first a = t+1) :
    (markedMemoryIndexedGhostQueue queue born last t).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨markedMemoryRetainedQueue_nodup queue _ hq,hb,?_⟩
  intro a ha b hbm hab
  subst b
  have hqa := (markedMemoryRetainedQueue_filter_mem queue (fun a => t < last a) a).mp ha |>.1
  have h₀ := hfirst a hqa
  have h₁ := hborn a hbm
  omega

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes} {B : ℕ}

/-- The raw target memory is exactly the canonical retained queue followed
by its ordered newly anchored birth queue; no multiset quotient is used. -/
theorem markedMemoryGhostTargetMemory_list (m : MarkedRawMemory P B)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (del : MarkedRawGhostDeletion m)
    (l : MarkedRawGhostBirthSizes m del) (births : MarkedRawGhostBirthLabels l) (j : J) :
    List.ofFn ((markedRawGhostTargetMemory m z hz del l births).2 j) =
      List.ofFn (fun k : Fin (markedRawGhostSurvivors m del j).card =>
        m.2 j ((markedRawGhostSurvivors m del j).orderEmbOfFin rfl k)) ++
      List.ofFn (fun k : Fin (l.1 j : ℕ) => markedRawAnchoredParticle (P j) (births j k) z hz) := by
  change List.ofFn (Fin.append
    (fun k => m.2 j ((markedRawGhostSurvivors m del j).orderEmbOfFin rfl k))
    (fun k => markedRawAnchoredParticle (P j) (births j k) z hz)) = _
  exact List.ofFn_fin_append _ _


end
end ArtinMatthews
