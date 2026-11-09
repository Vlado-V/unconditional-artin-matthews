module

public import ArtinMatthews.GiantCandidateSlotError
public import Mathlib.NumberTheory.DirichletCharacter.Bounds


set_option backward.privateInPublic true
@[expose] public section

/-! The literal tuple difference is bounded by positive products with
one discrepancy slot and all other slots bounded by the rough envelope. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

def giantCandidatePositiveTupleMass {j : ℕ} (N : ℕ) (i : Fin j) (d u : ℕ → ℝ) : ℝ :=
  ∑ t ∈ giantOrderedProductTuples j N,∏ k,if k=i then d (t k) else u (t k)

private theorem giantCandidateProductDifference_le {j : ℕ}
    (a b : Fin j → ℂ) (d u : Fin j → ℝ)
    (ha : ∀ i,‖a i‖ ≤ u i) (hb : ∀ i,‖b i‖ ≤ u i) (hd : ∀ i,‖a i-b i‖ ≤ d i) :
    ‖(∏ i,a i)-(∏ i,b i)‖ ≤ ∑ i,∏ k,if k=i then d k else u k := by
  classical
  have h := prod_sub_ordered univ a (fun i => a i-b i)
  simp only [sub_sub_cancel] at h
  have heq : (∏ i,a i)-(∏ i,b i) =
      ∑ i,(a i-b i)*(∏ k : Fin j with k < i,b k)*(∏ k : Fin j with i < k,a k) := by
    linear_combination -h
  rw [heq]
  refine (norm_sum_le _ _).trans (sum_le_sum (fun i _ => ?_))
  have hd₀ := (norm_nonneg _).trans (hd i)
  have hu₀ (k : Fin j) := (norm_nonneg _).trans (ha k)
  have hdis : Disjoint (univ.filter (fun k : Fin j => k < i)) (univ.filter (fun k : Fin j => i < k)) := by
    apply disjoint_left.mpr
    intro k hl hr
    exact (lt_asymm (mem_filter.mp hl).2) (mem_filter.mp hr).2
  have hunion : (univ.filter (fun k : Fin j => k < i)) ∪ (univ.filter (fun k : Fin j => i < k)) =
      univ.erase i := by
    ext k
    simp only [mem_union,mem_filter,mem_univ,true_and,mem_erase,and_true]
    exact ne_iff_lt_or_gt.symm
  simp only [norm_mul,norm_prod]
  calc
    _ ≤ d i*(∏ k : Fin j with k < i,u k)*(∏ k : Fin j with i < k,u k) := by
      apply mul_le_mul
      · exact mul_le_mul (hd i) (prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun k _ => hb k))
          (prod_nonneg (fun _ _ => norm_nonneg _)) hd₀
      · exact prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun k _ => ha k)
      · exact prod_nonneg (fun _ _ => norm_nonneg _)
      · exact mul_nonneg hd₀ (prod_nonneg (fun k _ => hu₀ k))
    _ = d i * ∏ k ∈ univ.erase i,u k := by rw [mul_assoc,← prod_union hdis,hunion]
    _ = _ := by
      rw [← mul_prod_erase univ (fun k => if k=i then d k else u k) (mem_univ i),ite_eq_left rfl]
      apply congrArg (fun r => d i*r)
      exact prod_congr rfl (fun k hk => (ite_eq_right (mem_erase.mp hk).1).symm)

theorem giant_ordinary_proxy_sub_stripped_norm_le {J : Type*} [Fintype J] {q : ℕ}
    (P : ℝ → Finset ℕ) (e : J → ℝ) (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    (Φ : ℝ → ℝ) (T γ : ℝ) (j : ℕ) (x C : ℝ) (hC : 0 ≤ C) (hz : 1 < x^γ)
    (hw : ∀ n : ℕ,n ≤ ⌊T*x⌋₊ → ‖markedExtractionWeight e G Φ x n‖ ≤ C) :
    let W := Real.exp ((Real.log x)^(6/25:ℝ))
    let z := x^γ
    ‖giantOrdinaryProxyTupleSum e χ G Φ T γ j x -
      giantOrdinaryStrippedProxyTupleSum P e χ G Φ T γ j x‖ ≤
      C*∑ i : Fin j,giantCandidatePositiveTupleMass ⌊T*x⌋₊ i
        (fun m => ‖giantRoughSlotCoefficient W z m -
          giantCandidateStrippedSlotCoefficient (P x) W z m‖) (giantCandidateProxyEnvelope W z) := by
  classical
  let W := Real.exp ((Real.log x)^(6/25:ℝ))
  let z := x^γ
  let N := ⌊T*x⌋₊
  let S := giantOrderedProductTuples j N
  let w (t : Fin j → ℕ) := markedExtractionWeight e G Φ x (∏ i,t i)
  let a (m : ℕ) := giantRoughSlotCoefficient W z m
  let b (m : ℕ) := giantCandidateStrippedSlotCoefficient (P x) W z m
  let u := giantCandidateProxyEnvelope W z
  let d (m : ℕ) := ‖a m-b m‖
  let F (t : Fin j → ℕ) := (∏ i,χ (t i)*a (t i))-(∏ i,χ (t i)*b (t i))
  have ha (m : ℕ) : ‖χ m*a m‖ ≤ u m := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans
      (giantRoughSlotCoefficient_norm_le_envelope (W:=W) hz m)
  have hb (m : ℕ) : ‖χ m*b m‖ ≤ u m := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans
      (giantCandidateStrippedSlotCoefficient_norm_le_envelope (P x) (W:=W) hz m)
  have hd (m : ℕ) : ‖χ m*a m-χ m*b m‖ ≤ d m := by
    rw [← mul_sub,norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
  have hfac : 1 ≤ ‖(j.factorial:ℂ)‖ := by
    rw [Complex.norm_natCast]
    exact_mod_cast Nat.factorial_pos j
  change ‖(∑ t ∈ S,w t*∏ i,χ (t i)*a (t i))/j.factorial-
    (∑ t ∈ S,w t*∏ i,χ (t i)*b (t i))/j.factorial‖ ≤
      C*∑ i : Fin j,giantCandidatePositiveTupleMass N i d u
  rw [← sub_div,← sum_sub_distrib,norm_div]
  simp_rw [← mul_sub]
  change ‖∑ t ∈ S,w t*F t‖/‖(j.factorial:ℂ)‖ ≤ _
  calc
    _ ≤ ‖∑ t ∈ S,w t*F t‖ := div_le_self (norm_nonneg _) hfac
    _ ≤ ∑ t ∈ S,‖w t‖*‖F t‖ := by
      simp only [← norm_mul]
      exact norm_sum_le _ _
    _ ≤ ∑ t ∈ S,C*(∑ i,∏ k,if k=i then d (t k) else u (t k)) := by
      apply sum_le_sum
      intro t ht
      exact mul_le_mul (hw _ (mem_giantOrderedProductTuples.mp ht).2)
        (giantCandidateProductDifference_le (fun i => χ (t i)*a (t i)) (fun i => χ (t i)*b (t i))
          (fun i => d (t i)) (fun i => u (t i)) (fun i => ha (t i)) (fun i => hb (t i)) (fun i => hd (t i)))
        (norm_nonneg _) hC
    _ = _ := by rw [← mul_sum,sum_comm]; rfl

end
end ArtinMatthews
