module

public import OAI.NumberTheory.Jacobsthal.Estimates.BonferroniBlocks
public import Mathlib.Analysis.SpecialFunctions.Pow.Real


set_option backward.privateInPublic true
@[expose] public section

/-! A fixed even Bonferroni polynomial majorizes one exact count.
The first omitted term has the genuine binomial normalization. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators
open OAI.Erdos970.NumberTheoryLean.BonferroniBlocks

def giantCandidatePointCountPoly (k r n : ℕ) : ℝ :=
  ∑ l∈range (r+1),(-1:ℝ)^l*((k+l).choose k:ℝ)*(n.choose (k+l):ℝ)

def giantCandidatePointCountDelta (k n : ℕ) : ℝ :=
  if n=k then 1 else 0

theorem giantCandidatePointCountDelta_nonneg (k n : ℕ) :
    0≤giantCandidatePointCountDelta k n := by
  unfold giantCandidatePointCountDelta
  split_ifs <;> norm_num

theorem giantCandidatePointCountDelta_le_one (k n : ℕ) :
    giantCandidatePointCountDelta k n≤1 := by
  unfold giantCandidatePointCountDelta
  split_ifs <;> norm_num

theorem giantCandidatePointCount_choose_mul (n k l : ℕ) :
    (n.choose (k+l):ℝ)*((k+l).choose k:ℝ) = (n.choose k:ℝ)*((n-k).choose l:ℝ) := by
  have h := Nat.choose_mul (n:=n) (k:=k+l) (s:=k) (Nat.le_add_right k l)
  rw [Nat.add_sub_cancel_left] at h
  exact_mod_cast h

theorem giantCandidatePointCountPoly_eq (k r n : ℕ) :
    giantCandidatePointCountPoly k r n = (n.choose k:ℝ)*alternatingChoose r (n-k) := by
  unfold giantCandidatePointCountPoly alternatingChoose
  rw [mul_sum]
  apply sum_congr rfl
  intro l _
  calc
    _ = (-1:ℝ)^l*((n.choose (k+l):ℝ)*((k+l).choose k:ℝ)) := by ring
    _ = _ := by rw [giantCandidatePointCount_choose_mul]; ring

private theorem giantCandidatePointCount_delta_mul (k n : ℕ) :
    (n.choose k:ℝ)*(if n-k=0 then 1 else 0) = giantCandidatePointCountDelta k n := by
  unfold giantCandidatePointCountDelta
  by_cases hn : n=k
  · subst n
    simp
  · by_cases hk : k≤n
    · have hz : n-k≠0 := by omega
      simp only [ite_eq_right hz,ite_eq_right hn,mul_zero]
    · simp only [Nat.choose_eq_zero_of_lt (lt_of_not_ge hk),Nat.cast_zero,zero_mul,ite_eq_right hn]

theorem giantCandidatePointCountPoly_bounds (k b n : ℕ) :
    giantCandidatePointCountDelta k n ≤ giantCandidatePointCountPoly k (2*b) n ∧
      giantCandidatePointCountPoly k (2*b) n ≤ giantCandidatePointCountDelta k n+
        ((k+(2*b+1)).choose k:ℝ)*(n.choose (k+(2*b+1)):ℝ) := by
  have h := alternatingChoose_bounds b (n-k)
  have hgap := alternatingChoose_gap b (n-k)
  have hup : alternatingChoose (2*b) (n-k) ≤ (if n-k=0 then 1 else 0)+((n-k).choose (2*b+1):ℝ) :=
    by linarith only [h.1,hgap]
  rw [giantCandidatePointCountPoly_eq]
  constructor
  · rw [← giantCandidatePointCount_delta_mul]
    exact mul_le_mul_of_nonneg_left h.2 (Nat.cast_nonneg _)
  · have hm := mul_le_mul_of_nonneg_left hup (Nat.cast_nonneg (α:=ℝ) (n.choose k))
    rw [mul_add,giantCandidatePointCount_delta_mul,← giantCandidatePointCount_choose_mul,
      mul_comm (n.choose (k+(2*b+1)):ℝ)] at hm
    exact hm

theorem giantCandidateBinomialFactorial_error (C : ℝ) (k r : ℕ) :
    ((k+r).choose k:ℝ)*(C^(k+r)/((k+r).factorial:ℝ)) =
      (C^k/(k.factorial:ℝ))*(C^r/(r.factorial:ℝ)) := by
  have hn := Nat.choose_mul_factorial_mul_factorial (n:=k+r) (k:=k) (Nat.le_add_right k r)
  rw [Nat.add_sub_cancel_left] at hn
  have h : ((k+r).choose k:ℝ)*(k.factorial:ℝ)*(r.factorial:ℝ) = ((k+r).factorial:ℝ) := by
    exact_mod_cast hn
  have hr : ((k+r).choose k:ℝ)/((k+r).factorial:ℝ) =
      1/((k.factorial:ℝ)*(r.factorial:ℝ)) := by
    rw [div_eq_div_iff (by positivity : ((k+r).factorial:ℝ)≠0)
      (by positivity : (k.factorial:ℝ)*(r.factorial:ℝ)≠0)]
    simpa only [mul_assoc,one_mul] using h
  calc
    _ = C^(k+r)*(((k+r).choose k:ℝ)/((k+r).factorial:ℝ)) := by ring
    _ = _ := by rw [hr,pow_add]; ring

end
end ArtinMatthews
