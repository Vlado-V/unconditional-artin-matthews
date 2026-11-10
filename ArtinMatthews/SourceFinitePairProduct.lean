module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Pair cancellation for the directed finite source factors. This
groups each unordered pair exactly once; it does not infer a product
equals one merely from its square. -/
namespace ArtinMatthews.SourceCRTNormalization

open scoped BigOperators Classical
variable {ι G : Type*} [CommMonoid G]

theorem sourceFiniteDirectedPairs_cancel (S : Finset ι) (F : ι → ι → G)
    (hdiag : ∀ i ∈ S, F i i = 1)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → F i j * F j i = 1) :
    (∏ i ∈ S, ∏ j ∈ S, F i j) = 1 := by
  classical
  revert hdiag hpair
  induction S using Finset.induction_on with
  | empty =>
    intro _ _
    simp only [Finset.prod_empty]
  | @insert a S ha ih =>
    intro hdiag hpair
    have hdiagS : ∀ i ∈ S, F i i = 1 := fun i hi => hdiag i (Finset.mem_insert_of_mem hi)
    have hpairS : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → F i j * F j i = 1 :=
      fun i hi j hj hij => hpair i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have hS := ih hdiagS hpairS
    calc
      _ = (F a a * ∏ j ∈ S, F a j) * ∏ i ∈ S, (F i a * ∏ j ∈ S, F i j) := by
        rw [Finset.prod_insert ha]
        simp_rw [Finset.prod_insert ha]
      _ = (∏ i ∈ S, F a i * F i a) * ∏ i ∈ S, ∏ j ∈ S, F i j := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hdiag a (Finset.mem_insert_self a S)]
        simp only [one_mul]
        ac_rfl
      _ = 1 := by
        rw [hS, mul_one]
        apply Finset.prod_eq_one
        intro i hi
        have hai : a ≠ i := by
          intro h
          subst i
          exact ha hi
        exact hpair a (Finset.mem_insert_self a S) i (Finset.mem_insert_of_mem hi) hai

end ArtinMatthews.SourceCRTNormalization
