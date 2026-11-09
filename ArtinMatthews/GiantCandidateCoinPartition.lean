module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! A finite Bernoulli partition with exact weights. The signed expansion
acts on each retained outcome separately. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
variable {ι : Type*} [DecidableEq ι]

def giantCoinOutcomeWeight (U : Finset ι) (s : ι → ℝ) (S : Finset ι) : ℝ :=
  (∏ i ∈ S,s i)*∏ i ∈ U \ S,(1-s i)

theorem giantCoinOutcomeWeight_nonneg (U : Finset ι) (s : ι → ℝ) (S : Finset ι)
    (hS : S ⊆ U) (hs : ∀ i ∈ U, s i ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ giantCoinOutcomeWeight U s S := by
  exact mul_nonneg (prod_nonneg (fun i hi => (hs i (hS hi)).1))
    (prod_nonneg (fun i hi => sub_nonneg.mpr (hs i (mem_sdiff.mp hi).1).2))

theorem giantCoinOutcomeWeight_sum (U : Finset ι) (s : ι → ℝ) :
    (∑ S ∈ U.powerset,giantCoinOutcomeWeight U s S)=1 := by
  calc
    _ = ∏ i ∈ U,(s i+(1-s i)) := (Finset.prod_add (s:=U) (f:=s) (g:=fun i => 1-s i)).symm
    _ = _ := by simp

theorem giantCoinOutcomeWeight_retained_failed (U : Finset ι) (R : Finset (Finset ι))
    (s : ι → ℝ) (hR : R ⊆ U.powerset) :
    (∑ S ∈ R,giantCoinOutcomeWeight U s S) +
      (∑ S ∈ U.powerset \ R,giantCoinOutcomeWeight U s S)=1 := by
  rw [add_comm,sum_sdiff hR,giantCoinOutcomeWeight_sum]

theorem giantCoinOutcomeWeight_expand (U : Finset ι) (s : ι → ℝ) (S : Finset ι) :
    giantCoinOutcomeWeight U s S =
      ∑ T ∈ (U \ S).powerset,(-1:ℝ)^T.card*(∏ i ∈ S ∪ T,s i) := by
  unfold giantCoinOutcomeWeight
  simp only [sub_eq_add_neg]
  rw [Finset.prod_one_add,Finset.mul_sum]
  apply sum_congr rfl
  intro T hT
  have hd : Disjoint S T := by
    refine disjoint_left.mpr ?_
    intro i hiS hiT
    exact (mem_sdiff.mp ((mem_powerset.mp hT) hiT)).2 hiS
  rw [prod_neg,prod_union hd]
  ring

end
end ArtinMatthews
