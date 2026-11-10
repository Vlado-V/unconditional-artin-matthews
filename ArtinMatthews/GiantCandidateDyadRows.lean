module

public import ArtinMatthews.GiantCandidateRoughDyad
public import ArtinMatthews.GiantCandidateThresholdDyad
public import ArtinMatthews.GiantCandidateRemovedCount
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Dyadic row masses for the unchanged rough envelope and the literal
one-slot difference. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

theorem giantCandidateEnvelope_dyad_sum (W z : ℝ) (N k : ℕ) :
    (∑ m ∈ primeExtractionDyadicBlock N k,giantCandidateProxyEnvelope W z m) =
      ((giantCandidateRoughDyad W z N k).card:ℝ)*giantCandidateSlotBound W z := by
  unfold giantCandidateProxyEnvelope giantCandidateRoughDyad
  rw [← sum_filter,sum_const,nsmul_eq_mul]

theorem giantCandidateDifference_dyad_sum_le
    (P : Finset ℕ) (hP : ∀ p ∈ P,p.Prime) {W z L : ℝ}
    (hz : 1 < z) (hL : 0 < L)
    (hPtop : ∀ p ∈ P,(p:ℝ) ≤ Real.exp (L^(9/20:ℝ)))
    (N k : ℕ) (hrough : ((giantCandidateRoughDyad W z N k).card:ℝ) ≤
      4*(2:ℝ)^k*markedSieveEulerProduct W) :
    let R := L^(9/10:ℝ)
    let A := giantCandidateSlotBound W z
    let V := markedSieveEulerProduct W
    let H := (2:ℝ)^k
    (∑ m ∈ primeExtractionDyadicBlock N k,
      ‖giantRoughSlotCoefficient W z m-giantCandidateStrippedSlotCoefficient P W z m‖) ≤
      2*A*(8*H*L^(-(9/20:ℝ))) +
        2*A*(if k ∈ giantCandidateThresholdDyadIndices (Real.log z) R then 4*H*V else 0) +
        (A*R/Real.log z)*(4*H*V) := by
  let R := L^(9/10:ℝ)
  let A := giantCandidateSlotBound W z
  let V := markedSieveEulerProduct W
  let H := (2:ℝ)^k
  let T := primeExtractionDyadicBlock N k
  let S := giantCandidateRoughDyad W z N k
  let I := giantCandidateThresholdDyadIndices (Real.log z) R
  let B := S.filter (fun m => R < giantCandidateRemovedLog P m)
  let C := S.filter (fun m : ℕ => Real.log (m:ℝ) ≤ Real.log z+R)
  let d (m : ℕ) := ‖giantRoughSlotCoefficient W z m-giantCandidateStrippedSlotCoefficient P W z m‖
  have hR : 0 ≤ R := Real.rpow_nonneg hL.le _
  have hA : 0 ≤ A := giantCandidateSlotBound_nonneg hz
  have hA₂ : 0 ≤ 2*A := mul_nonneg (by norm_num) hA
  have hA₃ : 0 ≤ A*R/Real.log z := div_nonneg (mul_nonneg hA hR) (Real.log_pos hz).le
  have hST : S ⊆ T := filter_subset _ _
  have hB : (B.card:ℝ) ≤ 8*H*L^(-(9/20:ℝ)) := by
    have hsub : B ⊆ T.filter (fun m => R < giantCandidateRemovedLog P m) :=
      fun m hm => mem_filter.mpr ⟨hST (mem_filter.mp hm).1,(mem_filter.mp hm).2⟩
    exact (Nat.cast_le.mpr (card_le_card hsub)).trans (giantCandidateLargeRemovalDyad_card_le hL P hP hPtop N k)
  have hC : (C.card:ℝ) ≤ if k ∈ I then 4*H*V else 0 := by
    by_cases hk : k ∈ I
    · rw [ite_eq_left hk]
      have hCS : C ⊆ S := filter_subset _ _
      exact (Nat.cast_le.mpr (card_le_card hCS)).trans hrough
    · rw [ite_eq_right hk]
      have hnil : C = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro m hm
        obtain ⟨hms,hhi⟩ := mem_filter.mp hm
        have hs : GiantCandidateProxySupport W z m := (mem_filter.mp hms).2
        have hlo := Real.log_lt_log (zero_lt_one.trans hz) hs.1
        exact hk (giantCandidateThresholdDyad_mem (Real.log_pos hz).le (hST hms) hlo hhi)
      rw [hnil,card_empty,Nat.cast_zero]
  have hsumB : (∑ m ∈ S,2*A*(if R < giantCandidateRemovedLog P m then 1 else 0)) =
      2*A*(B.card:ℝ) := by
    rw [← mul_sum,← sum_filter,sum_const,nsmul_eq_mul,mul_one]
  have hsumC : (∑ m ∈ S,2*A*(if Real.log (m:ℝ) ≤ Real.log z+R then 1 else 0)) =
      2*A*(C.card:ℝ) := by
    rw [← mul_sum,← sum_filter,sum_const,nsmul_eq_mul,mul_one]
  change (∑ m ∈ T,d m) ≤ 2*A*(8*H*L^(-(9/20:ℝ))) +
    2*A*(if k ∈ I then 4*H*V else 0)+(A*R/Real.log z)*(4*H*V)
  calc
    _ = ∑ m ∈ S,d m := by
      symm
      apply sum_subset hST
      intro m hm hms
      have hs : ¬GiantCandidateProxySupport W z m := fun h => hms (mem_filter.mpr ⟨hm,h⟩)
      simp only [d,giantRoughSlotCoefficient_eq_zero_of_not_support W z m hs,
        giantCandidateStrippedSlotCoefficient_eq_zero_of_not_support P W z m hs,sub_self,norm_zero]
    _ ≤ ∑ m ∈ S,(2*A*(if R < giantCandidateRemovedLog P m then 1 else 0) +
          2*A*(if Real.log (m:ℝ) ≤ Real.log z+R then 1 else 0)+A*R/Real.log z) :=
      sum_le_sum (fun _ hm => giantCandidateSlotError_le P hz hR (mem_filter.mp hm).2)
    _ = 2*A*(B.card:ℝ)+2*A*(C.card:ℝ)+(A*R/Real.log z)*(S.card:ℝ) := by
      rw [sum_add_distrib,sum_add_distrib,hsumB,hsumC,sum_const,nsmul_eq_mul,mul_comm (S.card:ℝ)]
    _ ≤ _ := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hB hA₂)
      (mul_le_mul_of_nonneg_left hC hA₂)) (mul_le_mul_of_nonneg_left hrough hA₃)

end
end ArtinMatthews
