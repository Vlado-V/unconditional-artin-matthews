module

public import ArtinMatthews.GiantCandidateBoundedCountTests
public import ArtinMatthews.GiantCandidateModelMomentRealization
public import ArtinMatthews.GiantCandidateUniformJointMoment


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform bounded tests of actual rough-box hit counts agree with
the genuine independent residue model. All orders used in the proof
are chosen before the large-parameter limit. -/

namespace ArtinMatthews
noncomputable section
open Finset Filter
open scoped BigOperators Topology

theorem giant_candidate_actual_bounded_count_tests_uniform
    {ι : Type*} [Fintype ι] [DecidableEq ι] (side : ι → GiantCandidateHitSide)
    (τ : ℝ) (hτ : 0<τ) {j : ℕ} (hj : 0<j) {B : ℝ} (hB : 0≤B)
    {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ x : ℝ in atTop,∀ G : ι → Finset ℕ,(∀ i,G i ⊆ giantCandidateFullPrimes x) →
      Pairwise (fun i l => side i=side l → Disjoint (G i) (G l)) →
      (∀ i,(∑ p∈G i,1/(p:ℝ))≤B) →
      ∃ hG : ∀ i p,p∈G i → p.Prime,
        ∀ H : Fin j → ℕ,(∀ v,x^τ≤(H v:ℝ)) →
        ∀ f : (ι → ℕ) → ℝ,(∀ k,|f k|≤1) →
        let W := Real.exp ((Real.log x)^(6/25:ℝ))
        let S (v : Fin j) := giantCandidateRoughFullDyad W (H v)
        |(𝔼 t∈Fintype.piFinset S,f (giantCandidateActualHitCounts G side t))-
          (𝔼 t∈giantCandidateModelResidueTuples G hG j,f (giantCandidateModelHitCounts G side t))|≤δ := by
  let C := (j:ℝ)*B
  have hC : 0≤C := mul_nonneg (Nat.cast_nonneg _) hB
  obtain ⟨K,η,hη,hTest⟩ := giantCandidateBoundedCountTests_from_moments ι hC hδ
  let E := giantCandidateCountVectors ι K
  have hRel := (eventually_all_finset E).mpr (fun k _ =>
    giant_candidate_actual_joint_binomial_moment_eventually side k τ 1 hτ zero_le_one j)
  have hAbs := (eventually_all_finset E).mpr (fun k _ =>
    giant_candidate_actual_joint_binomial_moment_uniform side k τ hτ hj hB hη)
  have hpow : Tendsto (fun x : ℝ => (1+(Real.log x)^(-(1:ℝ)))^j) atTop (𝓝 1) := by
    have ht := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1)).comp Real.tendsto_log_atTop
    have hc : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (𝓝 (1:ℝ)) := tendsto_const_nhds
    simpa only [Function.comp_apply,add_zero,one_pow] using (hc.add ht).pow j
  filter_upwards [hRel,hAbs,hpow.eventually (Iio_mem_nhds (by norm_num : (1:ℝ)<2)),
    giantCandidateFullPrimes_prime_upper_eventually] with x hrel habs hsmall hP
  intro G hG hdis hmass
  let hG' (i : ι) (p : ℕ) (hp : p∈G i) : p.Prime := (hP p (hG i hp)).1
  refine ⟨hG',?_⟩
  intro H hH f hf
  let W := Real.exp ((Real.log x)^(6/25:ℝ))
  let S (v : Fin j) := giantCandidateRoughFullDyad W (H v)
  let T := giantCandidateModelResidueTuples G hG' j
  let N := giantCandidateActualHitCounts (j:=j) G side
  let M := giantCandidateModelHitCounts (j:=j) G side
  have hmodel (k : ι → ℕ) : giantCandidateModelBinomialMoment j G side k hG'≤
      giantCandidateMomentEnvelope C k :=
    giantCandidateModelBinomialMoment_le hj G side k hG' hdis hB hmass
  have hmodel₀ (k : ι → ℕ) : 0≤giantCandidateModelBinomialMoment j G side k hG' :=
    giantCandidateModelBinomialMoment_nonneg j G side k hG'
  have hS : ∀ k∈E,giantCandidateCountMoment (Fintype.piFinset S) N k≤
      2*giantCandidateMomentEnvelope C k := by
    intro k hk
    obtain ⟨hprime,h⟩ := hrel k hk G hG
    change giantCandidateCountMoment (Fintype.piFinset S) (giantCandidateActualHitCounts G side) k≤_
    rw [giantCandidateActualHitCounts_moment_eq]
    calc
      _ ≤ (1+(Real.log x)^(-(1:ℝ)))^j*giantCandidateModelBinomialMoment j G side k hG' :=
        (h H hH).2
      _ ≤ 2*giantCandidateModelBinomialMoment j G side k hG' :=
        mul_le_mul_of_nonneg_right hsmall.le (hmodel₀ k)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hmodel k) (by norm_num)
  have hT : ∀ k∈E,giantCandidateCountMoment T M k≤2*giantCandidateMomentEnvelope C k := by
    intro k _
    change giantCandidateCountMoment (giantCandidateModelResidueTuples G hG' j)
      (giantCandidateModelHitCounts G side) k≤_
    rw [giantCandidateModelHitCounts_moment_eq]
    linarith only [hmodel k,hmodel₀ k]
  have hD : ∀ k∈E,|giantCandidateCountMoment (Fintype.piFinset S) N k-
      giantCandidateCountMoment T M k|≤η := by
    intro k hk
    obtain ⟨hprime,h⟩ := habs k hk G hG hdis hmass
    change |giantCandidateCountMoment (Fintype.piFinset S) (giantCandidateActualHitCounts G side) k-
      giantCandidateCountMoment (giantCandidateModelResidueTuples G hG' j)
        (giantCandidateModelHitCounts G side) k|≤η
    rw [giantCandidateActualHitCounts_moment_eq,giantCandidateModelHitCounts_moment_eq]
    exact h H hH
  exact hTest (Fintype.piFinset S) T N M hS hT hD f hf

end
end ArtinMatthews
