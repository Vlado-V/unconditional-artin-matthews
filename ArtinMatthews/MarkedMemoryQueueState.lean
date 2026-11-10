module

public import ArtinMatthews.MarkedMinorArcRawGhostState
public import ArtinMatthews.MarkedMemoryIndexedQueues
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

/-! Realize bounded ordered particle queues as the literal raw memory
state. No distinctness of numeric primes or particle values is required. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes} {B : ℕ}

def markedMemoryQueueSizes (queue : (j : J) → List (MarkedRawParticle (P j)))
    (hbound : (∑ j, (queue j).length) ≤ B) : MarkedRawMemorySizes J B :=
  ⟨fun j => ⟨(queue j).length,by
    have h := (Finset.single_le_sum (fun i _ => Nat.zero_le (queue i).length) (Finset.mem_univ j)).trans hbound
    omega⟩,hbound⟩

def markedMemoryQueueState (queue : (j : J) → List (MarkedRawParticle (P j)))
    (hbound : (∑ j, (queue j).length) ≤ B) : MarkedRawMemory P B :=
  ⟨markedMemoryQueueSizes queue hbound,fun j => (queue j).get⟩

theorem markedMemoryQueueState_list (queue : (j : J) → List (MarkedRawParticle (P j)))
    (hbound : (∑ j, (queue j).length) ≤ B) (j : J) :
    List.ofFn ((markedMemoryQueueState queue hbound).2 j) = queue j := List.ofFn_get _

/-- Exact ordered lists determine all bounded raw memory fields, including
the size vector; no quotient by particle values is taken. -/
theorem markedMemoryState_eq_of_lists (a b : MarkedRawMemory P B)
    (hlists : ∀ j, List.ofFn (a.2 j) = List.ofFn (b.2 j)) : a = b := by
  rcases a with ⟨ka,pa⟩
  rcases b with ⟨kb,pb⟩
  have hk : ka = kb := by
    apply Subtype.ext
    funext j
    apply Fin.ext
    have h := congrArg List.length (hlists j)
    simpa only [List.length_ofFn] using h
  cases hk
  have hp : pa = pb := by
    funext j
    exact List.ofFn_injective (hlists j)
  cases hp
  rfl

theorem markedMemoryQueueState_recover (m : MarkedRawMemory P B) :
    markedMemoryQueueState (fun j => List.ofFn (m.2 j))
      (by simpa only [List.length_ofFn] using m.1.2) = m := by
  apply markedMemoryState_eq_of_lists
  intro j
  exact markedMemoryQueueState_list _ _ j

/-- The original raw ghost target is the unique raw memory with these
ordered survivor-then-birth particle lists. -/
theorem markedMemoryGhostTarget_eq_queue (m : MarkedRawMemory P B)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (del : MarkedRawGhostDeletion m)
    (l : MarkedRawGhostBirthSizes m del) (births : MarkedRawGhostBirthLabels l) :
    markedRawGhostTargetMemory m z hz del l births =
      markedMemoryQueueState
        (fun j => List.ofFn (fun k : Fin (markedRawGhostSurvivors m del j).card =>
            m.2 j ((markedRawGhostSurvivors m del j).orderEmbOfFin rfl k)) ++
          List.ofFn (fun k : Fin (l.1 j : ℕ) => markedRawAnchoredParticle (P j) (births j k) z hz))
        (by simpa only [List.length_append, List.length_ofFn] using l.2) := by
  apply markedMemoryState_eq_of_lists
  intro j
  rw [markedMemoryQueueState_list]
  exact markedMemoryGhostTargetMemory_list m z hz del l births j

end
end ArtinMatthews
