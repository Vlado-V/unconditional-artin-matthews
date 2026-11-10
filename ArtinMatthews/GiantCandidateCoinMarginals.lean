module

public import ArtinMatthews.GiantCandidateCoinPartition
public import Mathlib.CategoryTheory.Category.Basic
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


set_option backward.privateInPublic true
@[expose] public section

/-! Forcing any set of success labels has exactly the product of their
conditional probabilities. The remaining outcomes form a full partition. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
variable {ι : Type*} [DecidableEq ι]

theorem giantCoinOutcomeWeight_forced (U : Finset ι) (s : ι → ℝ) (A : Finset ι)
    (hA : A ⊆ U) :
    (∑ S ∈ U.powerset.filter (fun S => A ⊆ S),giantCoinOutcomeWeight U s S) =
      ∏ i ∈ A,s i := by
  let W := U \ A
  let D := U.powerset.filter (fun S => A ⊆ S)
  have hdis (T : Finset ι) (hT : T ⊆ W) : Disjoint A T :=
    disjoint_left.mpr (fun _ ha ht => (mem_sdiff.mp (hT ht)).2 ha)
  have hrec (T : Finset ι) (hT : T ⊆ W) : (A ∪ T) \ A = T := by
    ext i
    simp only [mem_sdiff,mem_union]
    have hn : i ∈ T → i ∉ A := fun hi => (mem_sdiff.mp (hT hi)).2
    tauto
  have hsplit (T : Finset ι) (hT : T ⊆ W) :
      giantCoinOutcomeWeight U s (A ∪ T) =
        (∏ i ∈ A,s i)*giantCoinOutcomeWeight W s T := by
    have he : U \ (A ∪ T) = W \ T := by
      ext i
      simp only [W,mem_sdiff,mem_union]
      tauto
    unfold giantCoinOutcomeWeight
    rw [prod_union (hdis T hT),he,mul_assoc]
  change (∑ S ∈ D,giantCoinOutcomeWeight U s S) = _
  calc
    _ = ∑ T ∈ W.powerset,giantCoinOutcomeWeight U s (A ∪ T) := by
      symm
      apply sum_bij (fun T _ => A ∪ T)
      · intro T hT
        have ht := (mem_powerset.mp hT).trans sdiff_subset
        exact mem_filter.mpr ⟨mem_powerset.mpr (union_subset hA ht),subset_union_left⟩
      · intro T ht T' ht' he
        have hh := congrArg (fun S : Finset ι => S \ A) he
        simpa only [hrec T (mem_powerset.mp ht),hrec T' (mem_powerset.mp ht')] using hh
      · intro S hS
        obtain ⟨hU,hSA⟩ := mem_filter.mp hS
        have hT : S \ A ⊆ W := by
          intro i hi
          exact mem_sdiff.mpr ⟨(mem_powerset.mp hU) (mem_sdiff.mp hi).1,(mem_sdiff.mp hi).2⟩
        refine ⟨S \ A,mem_powerset.mpr hT,?_⟩
        ext i
        simp only [mem_union,mem_sdiff]
        have hs : i ∈ A → i ∈ S := fun h => hSA h
        tauto
      · intro T _
        rfl
    _ = (∏ i ∈ A,s i)*∑ T ∈ W.powerset,giantCoinOutcomeWeight W s T := by
      rw [Finset.mul_sum]
      exact sum_congr rfl (fun T hT => hsplit T (mem_powerset.mp hT))
    _ = _ := by rw [giantCoinOutcomeWeight_sum,mul_one]

theorem giantCoinOutcomeWeight_single (U : Finset ι) (s : ι → ℝ) {i : ι} (hi : i ∈ U) :
    (∑ S ∈ U.powerset.filter (fun S => i ∈ S),giantCoinOutcomeWeight U s S) = s i := by
  simpa only [singleton_subset_iff,prod_singleton] using
    giantCoinOutcomeWeight_forced U s {i} (singleton_subset_iff.mpr hi)

theorem giantCoinOutcomeWeight_pair (U : Finset ι) (s : ι → ℝ) {i j : ι}
    (hi : i ∈ U) (hj : j ∈ U) (hij : i ≠ j) :
    (∑ S ∈ U.powerset.filter (fun S => i ∈ S ∧ j ∈ S),giantCoinOutcomeWeight U s S) = s i*s j := by
  have hsub : ({i,j} : Finset ι) ⊆ U :=
    insert_subset_iff.mpr ⟨hi,singleton_subset_iff.mpr hj⟩
  have hn : i ∉ ({j} : Finset ι) := fun hi => hij (mem_singleton.mp hi)
  simpa only [insert_subset_iff,singleton_subset_iff,prod_insert hn,prod_singleton] using
    giantCoinOutcomeWeight_forced U s {i,j} hsub

end
end ArtinMatthews
