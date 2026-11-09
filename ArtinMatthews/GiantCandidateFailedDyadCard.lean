module

public import ArtinMatthews.GiantCandidateFailedBoxMean


set_option backward.privateInPublic true
@[expose] public section

/-! The actual full rough-box mass is the product of its true rough
coordinate counts. At positive-power heights those counts carry the
same Euler factor as the reciprocal in the original slot weights. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section

theorem giantCandidateFullRoughBox_card_eventually {τ : ℝ} (hτ : 0 < τ) (j : ℕ) :
    ∀ᶠ x : ℝ in atTop,∀ H : Fin j → ℕ,(∀ i,x^τ ≤ (H i:ℝ)) →
      let V := markedSieveEulerProduct (Real.exp ((Real.log x)^(6/25:ℝ)))
      0 < (giantCandidateFullRoughBox x H).card ∧
        ((giantCandidateFullRoughBox x H).card:ℝ) ≤ (2*V)^j*∏ i,(H i:ℝ) := by
  filter_upwards [giant_candidate_rough_full_dyad_ratio_eventually τ 0 0 hτ le_rfl le_rfl,
    eventually_gt_atTop (0:ℝ)] with x hratio hx
  intro H hH
  let W := Real.exp ((Real.log x)^(6/25:ℝ))
  let V := markedSieveEulerProduct W
  let S (i : Fin j) := giantCandidateRoughFullDyad W (H i)
  have hrow (i : Fin j) :
      (H i:ℝ)*V/2 ≤ ((S i).card:ℝ) ∧ ((S i).card:ℝ) ≤ 2*((H i:ℝ)*V) := by
    have h := hratio (H i) 1 0 (by decide) (by simp)
      (fun p _ => Nat.coprime_one_right p) (hH i)
    exact ⟨h.1,h.2.1⟩
  have hpos (i : Fin j) : 0 < (S i).card := by
    have hi := (Real.rpow_pos_of_pos hx τ).trans_le (hH i)
    have hc : (0:ℝ) < (S i).card :=
      (div_pos (mul_pos hi (markedSieveEulerProduct_pos W)) (by norm_num)).trans_le (hrow i).1
    exact Nat.cast_pos.mp hc
  change 0 < (Fintype.piFinset S).card ∧
    ((Fintype.piFinset S).card:ℝ) ≤ (2*V)^j*∏ i,(H i:ℝ)
  rw [Fintype.card_piFinset,Nat.cast_prod]
  refine ⟨prod_pos (fun i _ => hpos i),?_⟩
  calc
    _ ≤ ∏ i,(2*V)*(H i:ℝ) := by
      apply prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
      intro i _
      exact (hrow i).2.trans_eq (by ring)
    _ = _ := by rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin]

end
end ArtinMatthews
