module

public import ArtinMatthews.GiantCandidateCountMoments
public import Mathlib.Data.Rat.Star


set_option backward.privateInPublic true
@[expose] public section

/-! A bounded test loses only the first-moment tail when the count
vector is cut off at a fixed finite box. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

def giantCandidateCountTruncatedMean {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset Ω) (N : Ω → ι → ℕ) (a : ℕ) (f : (ι → ℕ) → ℝ) : ℝ :=
  ∑ k∈giantCandidateCountVectors ι a,f k*(𝔼 t∈S,giantCandidateCountVectorDelta k (N t))

theorem giantCandidateCountTruncatedMean_eq {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset Ω) (N : Ω → ι → ℕ) (a : ℕ) (f : (ι → ℕ) → ℝ) :
    giantCandidateCountTruncatedMean S N a f =
      𝔼 t∈S,if N t∈giantCandidateCountVectors ι a then f (N t) else 0 := by
  unfold giantCandidateCountTruncatedMean
  simp_rw [mul_expect,← expect_sum_comm]
  apply expect_congr rfl
  intro t _
  let E := giantCandidateCountVectors ι a
  change (∑ k∈E,f k*giantCandidateCountVectorDelta k (N t)) = if N t∈E then f (N t) else 0
  by_cases ht : N t∈E
  · rw [ite_eq_left ht, sum_eq_single_of_mem (N t) ht]
    · rw [giantCandidateCountVectorDelta,ite_eq_left rfl,mul_one]
    · intro k _ hk
      rw [giantCandidateCountVectorDelta,ite_eq_right (Ne.symm hk),mul_zero]
  · rw [ite_eq_right ht]
    apply sum_eq_zero
    intro k hk
    have he : N t≠k := fun h => ht (h.symm ▸ hk)
    rw [giantCandidateCountVectorDelta,ite_eq_right he,mul_zero]

theorem giantCandidateCountMean_tail {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset Ω) (N : Ω → ι → ℕ) (a : ℕ) (f : (ι → ℕ) → ℝ)
    (hf : ∀ n,|f n|≤1) (C : ℝ) (hC : ∀ i,(𝔼 t∈S,(N t i:ℝ))≤2*C) :
    |(𝔼 t∈S,f (N t))-giantCandidateCountTruncatedMean S N a f|≤
      2*C*(Fintype.card ι:ℝ)/((a:ℝ)+1) := by
  let E := giantCandidateCountVectors ι a
  let b := (a:ℝ)+1
  have hb : 0<b := by dsimp only [b]; positivity
  have ht (t : Ω) : |f (N t)-(if N t∈E then f (N t) else 0)|≤∑ i,(N t i:ℝ)/b := by
    by_cases h : N t∈E
    · rw [ite_eq_left h,sub_self,abs_zero]
      exact sum_nonneg (fun i _ => div_nonneg (Nat.cast_nonneg _) hb.le)
    · rw [ite_eq_right h,sub_zero]
      have he : ∃ i,a<N t i := by
        by_contra hn
        exact h (mem_giantCandidateCountVectors.mpr (fun i => le_of_not_gt (fun hi => hn ⟨i,hi⟩)))
      obtain ⟨i,hi⟩ := he
      have hi' : b≤(N t i:ℝ) := by
        change (a:ℝ)+1≤(N t i:ℝ)
        exact_mod_cast Nat.succ_le_of_lt hi
      exact (hf _).trans (((le_div_iff₀ hb).mpr (by simpa only [one_mul] using hi')).trans
        (single_le_sum (fun i _ => div_nonneg (Nat.cast_nonneg _) hb.le) (mem_univ i)))
  rw [giantCandidateCountTruncatedMean_eq,← expect_sub_distrib]
  calc
    _ ≤ 𝔼 t∈S,|f (N t)-(if N t∈E then f (N t) else 0)| := abs_expect_le _ _
    _ ≤ 𝔼 t∈S,∑ i,(N t i:ℝ)/b := expect_le_expect (fun t _ => ht t)
    _ ≤ ∑ _i : ι,2*C/b := by
      rw [expect_sum_comm]
      apply sum_le_sum
      intro i _
      rw [← expect_div]
      exact div_le_div_of_nonneg_right (hC i) hb.le
    _ = _ := by
      rw [sum_const,nsmul_eq_mul,card_univ]
      change (Fintype.card ι:ℝ)*(2*C/b)=2*C*(Fintype.card ι:ℝ)/b
      ring

end
end ArtinMatthews
