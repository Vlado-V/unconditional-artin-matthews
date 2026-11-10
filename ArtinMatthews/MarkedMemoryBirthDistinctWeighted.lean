module

public import ArtinMatthews.MarkedBirthDistinctPermutation
public import ArtinMatthews.MarkedMemoryHistoryBirths
public import ArtinMatthews.MarkedMemoryPotentialBirths
public import ArtinMatthews.MarkedBirthDistinctWeighted
public import ArtinMatthews.MarkedBirthRankCount
public import ArtinMatthews.MarkedMemoryPotentialDistinct
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

/-! The fixed-address inclusion-exclusion applied to the original finite
chronological histories. The weight is arbitrary: all actual coefficients,
cutoffs and boundary factors may remain inside it. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

local instance potentialPermFintype
    {J : Type*} [Fintype J] [DecidableEq J] (M B n : ℕ) :
    Fintype (Equiv.Perm (MarkedMemoryPotentialAddress J M B n)) :=
  @Equiv.instFintype (MarkedMemoryPotentialAddress J M B n)
    (MarkedMemoryPotentialAddress J M B n) inferInstance inferInstance inferInstance inferInstance

theorem markedMemoryHistoryBirthDistinct_weighted_permutation_sum
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (s : MarkedRawState P (pads+1) B Z)
    (F : MarkedMemoryChronologicalHistory hZ n s → ℂ) :
    (∑ h, if MarkedMemoryHistoryBirthDistinct hZ h then F h else 0) =
      ∑ σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B n),
        ((σ.sign : ℤ) : ℂ) *
          ∑ h, if MarkedBirthPermutationEvent (markedMemoryPotentialAddressValue hZ h) σ
            then F h else 0 := by
  simp_rw [markedMemoryHistoryBirthDistinct_iff_potential]
  exact markedBirthDistinct_weighted_permutation_sum
    (fun h : MarkedMemoryChronologicalHistory hZ n s => markedMemoryPotentialAddressValue hZ h) F

theorem markedMemoryHistoryBirthDistinct_boundary_permutation_sum
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (F : (s : MarkedRawState P (pads+1) B Z) → MarkedMemoryChronologicalHistory hZ n s → ℂ) :
    (∑ s, ∑ h, if MarkedMemoryHistoryBirthDistinct hZ h then F s h else 0) =
      ∑ σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B n),
        ((σ.sign : ℤ) : ℂ) *
          ∑ s, ∑ h, if MarkedBirthPermutationEvent (markedMemoryPotentialAddressValue hZ h) σ
            then F s h else 0 := by
  simp_rw [markedMemoryHistoryBirthDistinct_weighted_permutation_sum hZ]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.mul_sum]

theorem markedMemoryBirth_rank_operation_bound
    {J : Type*} [Fintype J] [DecidableEq J] (M B n : ℕ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B n)) :
    (σ.support.image markedMemoryPotentialOperation).card ≤ 2*markedBirthPermutationRank σ :=
  markedBirthPermutation_operations_le_twice_rank markedMemoryPotentialOperation σ

theorem markedMemoryBirth_rank_coefficient_bound
    {J : Type*} [Fintype J] [DecidableEq J] (M B n r : ℕ) :
    Fintype.card {σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B n) //
      markedBirthPermutationRank σ = r} ≤
        ((Fintype.card J*M+(n+1)*Fintype.card J*B+n*Fintype.card J)^2+1)^(2*r) := by
  have h := markedBirthPermutation_rank_card_bound
    (A := MarkedMemoryPotentialAddress J M B n) r
  simpa only [markedMemoryPotentialAddress_card, pow_two] using h

end ArtinMatthews
