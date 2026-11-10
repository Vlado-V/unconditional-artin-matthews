module

public import ArtinMatthews.MarkedMemoryPotentialPivots
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

/-! The exact rank-many pivot constraints split over initial draws and
the literal alternating ghost/edge stages. No potential absent birth is
removed from the guard, and stage counts have no inequality loss. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedMemoryPotentialPivot_earlier
    {J : Type*} [Fintype J] [DecidableEq J] {M B N : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N))
    {a : MarkedMemoryPotentialAddress J M B N}
    (ha : a∈markedMemoryPotentialNonpivots σ) :
    MarkedMemoryPotentialEarlier (markedMemoryPotentialPivot σ a) a :=
  @markedBirthChronologicalPivot_lt (MarkedMemoryPotentialAddress J M B N)
    inferInstance inferInstance markedMemoryPotentialChronologicalOrder σ a ha

theorem markedMemoryPotentialChronologicalTime_lt
    {J : Type*} {M B N : ℕ} (a : MarkedMemoryPotentialAddress J M B N) :
    markedMemoryPotentialChronologicalTime a < 2*N+2 := by
  rcases a with ⟨j,k⟩ | ⟨t,j,k⟩ | ⟨t,j⟩ <;>
    simp only [markedMemoryPotentialChronologicalTime] <;> omega

def markedMemoryStageNonpivots
    {J : Type*} [Fintype J] [DecidableEq J] {M B N : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) (t : ℕ) :
    Finset (MarkedMemoryPotentialAddress J M B N) :=
  (markedMemoryPotentialNonpivots σ).filter (fun a => markedMemoryPotentialChronologicalTime a=t)

theorem markedMemoryStageNonpivots_parent_earlier
    {J : Type*} [Fintype J] [DecidableEq J] {M B N : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) (t : ℕ)
    {a : MarkedMemoryPotentialAddress J M B N} (ha : a∈markedMemoryStageNonpivots σ t) :
    MarkedMemoryPotentialEarlier (markedMemoryPotentialPivot σ a) a :=
  markedMemoryPotentialPivot_earlier σ (Finset.mem_filter.mp ha).1

theorem markedMemoryStageNonpivots_card_sum
    {J : Type*} [Fintype J] [DecidableEq J] {M B N : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) :
    (∑ t ∈ Finset.range (2*N+2), (markedMemoryStageNonpivots σ t).card)=
      markedBirthPermutationRank σ := by
  rw [← markedMemoryPotentialNonpivots_card σ]
  symm
  exact Finset.card_eq_sum_card_fiberwise (fun a _ =>
    Finset.mem_range.mpr (markedMemoryPotentialChronologicalTime_lt a))

theorem markedMemoryStageNonpivots_atom_product
    {J : Type*} [Fintype J] [DecidableEq J] {M B N : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) (Δ : ℝ) :
    (∏ t ∈ Finset.range (2*N+2), Δ^(markedMemoryStageNonpivots σ t).card)=
      Δ^(markedBirthPermutationRank σ) := by
  rw [Finset.prod_pow_eq_pow_sum,markedMemoryStageNonpivots_card_sum]

end ArtinMatthews
