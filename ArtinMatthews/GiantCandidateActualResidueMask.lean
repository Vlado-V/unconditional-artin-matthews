module

public import ArtinMatthews.GiantCandidateTupleResidues
public import ArtinMatthews.GiantCandidateActualResidues


set_option backward.privateInPublic true
@[expose] public section

/-! Any fixed-prime residue event on the actual ordered product dyad
has multiplicative error uniformly in the event. -/

namespace ArtinMatthews
noncomputable section
open Finset Filter
open scoped BigOperators

theorem giant_candidate_actual_rough_residue_mask_eventually (τ A : ℝ)
    (hτ : 0 < τ) (hA : 0 ≤ A) (r j : ℕ) :
    ∀ᶠ x : ℝ in atTop,∀ U : Finset ℕ,U ⊆ giantCandidateFullPrimes x → U.card≤r →
      let Q := giantCandidateResidueModulus U
      ∀ (H : Fin j → ℕ) (E : Finset (Fin j → ZMod Q)),(∀ i,x^τ≤(H i:ℝ)) →
      let W := Real.exp ((Real.log x)^(6/25:ℝ))
      let S (i : Fin j) := giantCandidateRoughFullDyad W (H i)
      let ε := (Real.log x)^(-A)
      0 < (Fintype.piFinset S).card ∧
      (1-ε)^j*giantCandidateUniformResidueMass E ≤ giantCandidateTupleResidueMass S E ∧
      giantCandidateTupleResidueMass S E ≤ (1+ε)^j*giantCandidateUniformResidueMass E := by
  filter_upwards [giantCandidateActualResidueModulus_eventually r,
    giant_candidate_actual_rough_full_dyad_ratio_eventually τ A hτ hA r,
    eventually_gt_atTop (0:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ)]
    with x hmod hratio hx hL
  intro U hU hr Q H E hH
  let W := Real.exp ((Real.log x)^(6/25:ℝ))
  let S (i : Fin j) := giantCandidateRoughFullDyad W (H i)
  let ε := (Real.log x)^(-A)
  have hQ := (hmod U hU hr).1
  have hε : ε ≤ 1 := by
    simpa only [ε,Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hL (neg_nonpos.mpr hA)
  have hc (i : Fin j) : 0<(S i).card := by
    have h := (hratio U hU hr (H i) (0:ZMod Q) (hH i)).1
    have hh : (0:ℝ)<H i := (Real.rpow_pos_of_pos hx τ).trans_le (hH i)
    exact Nat.cast_pos.mp ((div_pos (mul_pos hh (markedSieveEulerProduct_pos W)) (by norm_num)).trans_le h)
  change 0 < (Fintype.piFinset S).card ∧
      (1-ε)^j*giantCandidateUniformResidueMass E ≤ giantCandidateTupleResidueMass S E ∧
      giantCandidateTupleResidueMass S E ≤ (1+ε)^j*giantCandidateUniformResidueMass E
  refine ⟨?_,giantCandidateTupleResidueMass_bounds hQ S E hε ?_⟩
  · rw [Fintype.card_piFinset]
    exact prod_pos (fun i _ => hc i)
  · intro i a
    exact (hratio U hU hr (H i) a (hH i)).2.2

end
end ArtinMatthews
