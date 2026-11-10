module

public import ArtinMatthews.GiantCandidateSquareFiber
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.NumberTheory.Chebyshev
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


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite removal of the candidate-square guard on the ordered
tuple sum or on the product-indexed allocated sum. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

theorem giantCandidateSquareTuples_guard_error_le (C : Finset ℕ) (X j : ℕ)
    (F : (Fin j → ℕ) → ℂ) {B : ℝ}
    (hF : ∀ t ∈ giantOrderedProductTuples j X, ‖F t‖ ≤ B) :
    ‖(∑ t ∈ giantOrderedProductTuples j X,F t) -
      ∑ t ∈ (giantOrderedProductTuples j X).filter (fun t => ∀ p ∈ C,¬p^2 ∣ ∏ i,t i),F t‖ ≤
        B*giantCandidateSquareFiberMass C X j := by
  classical
  let S := giantOrderedProductTuples j X
  let G := S.filter (fun t => ∀ p ∈ C,¬p^2 ∣ ∏ i,t i)
  let D := S.filter (fun t => ∃ p ∈ C,p^2 ∣ ∏ i,t i)
  have hD : S \ G = D := by
    ext t
    simp only [G,D,mem_sdiff,mem_filter]
    push Not
    tauto
  have hsub : G ⊆ S := filter_subset _ _
  have hsum : (∑ t ∈ S,F t)-(∑ t ∈ G,F t) = ∑ t ∈ D,F t := by
    rw [← sum_sdiff hsub (f:=F),hD]
    abel
  change ‖(∑ t ∈ S,F t)-(∑ t ∈ G,F t)‖ ≤ _
  rw [hsum]
  calc
    _ ≤ ∑ t ∈ D,‖F t‖ := norm_sum_le _ _
    _ ≤ ∑ _t ∈ D,B := sum_le_sum (fun t ht => hF t (mem_filter.mp ht).1)
    _ = B*giantCandidateSquareFiberMass C X j := by
      rw [giantCandidateSquareFiberMass_eq_tuple_card]
      simp only [D,S,sum_const,nsmul_eq_mul,mul_comm]

theorem giantCandidateSquareProducts_guard_error_le (C : Finset ℕ) (X j : ℕ)
    (F : ℕ → ℂ) {B : ℝ}
    (hF : ∀ n ∈ giantCandidateSquareExceptions C X,
      ‖F n‖ ≤ B*((giantOrderedProductFiber j n).card:ℝ)) :
    ‖(∑ n ∈ Ioc 0 X,F n) -
      ∑ n ∈ (Ioc 0 X).filter (fun n => ∀ p ∈ C,¬p^2 ∣ n),F n‖ ≤
        B*giantCandidateSquareFiberMass C X j := by
  classical
  let S := Ioc 0 X
  let G := S.filter (fun n => ∀ p ∈ C,¬p^2 ∣ n)
  let D := giantCandidateSquareExceptions C X
  have hD : S \ G = D := by
    ext n
    simp only [S,G,D,mem_sdiff,mem_filter,mem_Ioc,mem_giantCandidateSquareExceptions]
    push Not
    tauto
  have hsub : G ⊆ S := filter_subset _ _
  have hsum : (∑ n ∈ S,F n)-(∑ n ∈ G,F n) = ∑ n ∈ D,F n := by
    rw [← sum_sdiff hsub (f:=F),hD]
    abel
  change ‖(∑ n ∈ S,F n)-(∑ n ∈ G,F n)‖ ≤ _
  rw [hsum]
  calc
    _ ≤ ∑ n ∈ D,‖F n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ D,B*((giantOrderedProductFiber j n).card:ℝ) := sum_le_sum hF
    _ = B*giantCandidateSquareFiberMass C X j := (Finset.mul_sum _ _ _).symm

end
end ArtinMatthews
