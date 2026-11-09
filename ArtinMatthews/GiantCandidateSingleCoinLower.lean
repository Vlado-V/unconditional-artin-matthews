module

public import ArtinMatthews.GiantCandidateModelOneEachUnion
public import ArtinMatthews.GiantCandidateCoinModelPair


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine independent one-group coin expectation has a uniform
positive lower bound from its one-predecessor/one-product event. -/

namespace ArtinMatthews
noncomputable section
open Filter Finset
open scoped BigOperators

theorem giantCandidateSingleModelCoinMean_ge (P : Finset ℕ) (hP : ∀p∈P,p.Prime)
    {q : ℝ} (hq₀ : 0≤q) (hq₁ : q<1) {j : ℕ} (hj : 0<j)
    (hV₀ : Real.log 2/2≤bandReciprocalMass P) (hV₁ : bandReciprocalMass P≤1)
    (hlarge : ∀p∈P,4*(j:ℝ)≤(p:ℝ))
    (hsmall : ∀p∈P,(j:ℝ)/(p:ℝ)≤bandReciprocalMass P/2) :
    giantCandidateCoinScale q j*(Real.exp (-(4*(j:ℝ)))*(bandReciprocalMass P^2/4))≤
      giantCandidateSingleModelCoinMean P hP (giantCandidateCoinScale q j) q j := by
  classical
  let A : Fin 1 → Finset ℕ := fun _ => P
  let G := giantCandidateCoinModelBands A
  let U := giantCandidateSelectionPrimes G
  let side := giantCandidateCoinModelSides 1
  let hG : ∀i p,p∈G i→p.Prime := fun _ => hP
  let T := giantCandidateModelResidueTuples G hG j
  let M := giantCandidateModelOneEachUnion G hG j
  let V := bandReciprocalMass P
  let c := giantCandidateCoinScale q j
  let f := giantCandidateCoinModelValue A c q j 0
  have hc : 0<c := (giantCandidateCoinScale_bounds hq₀ hq₁ j hj).1
  have hV : 0<V := (div_pos (Real.log_pos (by norm_num)) (by norm_num)).trans_le hV₀
  have hU : U=P := giantCandidateSingleModelPrimes P
  have hsum : (∑ p : U,1/(p.val:ℝ))=V := by
    exact (sum_coe_sort U (fun p : ℕ => 1/(p:ℝ))).trans (by rw [hU]; rfl)
  have hlarge' (p : U) : 4*(j:ℝ)≤(p.val:ℝ) := hlarge p.val (hU ▸ p.property)
  have hsmall' (p : U) : (j:ℝ)/(p.val:ℝ)≤(∑ a : U,1/(a.val:ℝ))/2 := by
    rw [hsum]
    exact hsmall p.val (hU ▸ p.property)
  have hMass : Real.exp (-(4*(j:ℝ)))*(V^2/4)≤(M.card:ℝ)/(T.card:ℝ) := by
    have h := giantCandidateModelOneEachUnion_mass_ge G hG hj hlarge' hsmall'
      (hsum.trans_le hV₁)
    change Real.exp (-(4*(j:ℝ)))*((∑ p : U,1/(p.val:ℝ))^2/4)≤(M.card:ℝ)/(T.card:ℝ) at h
    rwa [hsum] at h
  have hf₀ (t : GiantCandidateModelResidueSpace G j) : 0≤f t :=
    (giantCandidateCoinCountTest_unitInterval A hq₀ hq₁ hj 0 hV₀ _).1
  have hf₁ (t : GiantCandidateModelResidueSpace G j) (ht : t∈M) : c≤f t := by
    obtain ⟨p,hp,htp⟩ := mem_biUnion.mp ht
    have hpair := (mem_filter.mp hp).2
    have hfull (i : Fin 1 × Bool) : G i=U := hU.symm
    have ha := giantCandidateModelOneEach_full_hitSet G hG side (0,true) (hfull _) hpair htp
    have hb := giantCandidateModelOneEach_full_hitSet G hG side (0,false) (hfull _) hpair htp
    have ha₁ : giantCandidateModelHitCounts G side t (0,true)=1 := by
      unfold giantCandidateModelHitCounts
      rw [ha,card_singleton]
    have hb₁ : giantCandidateModelHitCounts G side t (0,false)=1 := by
      unfold giantCandidateModelHitCounts
      rw [hb,card_singleton]
    change c≤giantCandidateCoinTest c q j V
      (giantCandidateModelHitCounts G side t (0,true)) (giantCandidateModelHitCounts G side t (0,false))
    rw [ha₁,hb₁,giantCandidateCoinTest_one_one c q j hV.ne']
    exact (le_div_iff₀ (pow_pos hV _)).mpr (mul_le_of_le_one_right hc.le (pow_le_one₀ hV.le hV₁))
  change c*(Real.exp (-(4*(j:ℝ)))*(V^2/4))≤𝔼 t∈T,f t
  rw [expect_eq_sum_div_card]
  calc
    _ ≤ c*((M.card:ℝ)/(T.card:ℝ)) := mul_le_mul_of_nonneg_left hMass hc.le
    _ = (∑ _t∈M,c)/(T.card:ℝ) := by rw [sum_const,nsmul_eq_mul]; ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact (sum_le_sum hf₁).trans
        (sum_le_sum_of_subset_of_nonneg (giantCandidateModelOneEachUnion_subset G hG j)
          (fun t _ _ => hf₀ t))

theorem giant_candidate_single_model_coin_mean_lower_eventually
    {q : ℝ} (hq₀ : 0≤q) (hq₁ : q<1) {j : ℕ} (hj : 0<j) :
    ∃ β : ℝ,0<β ∧ ∀ᶠ x : ℝ in atTop,∀ g : GiantCandidateGroupIndex x,
      ∀ hp : ∀p∈giantCandidateGroup x g,p.Prime,
        β≤giantCandidateSingleModelCoinMean (giantCandidateGroup x g) hp
          (giantCandidateCoinScale q j) q j := by
  let c := giantCandidateCoinScale q j
  let R := Real.exp (-(4*(j:ℝ)))
  let V₀ := Real.log 2/2
  let β := c*(R*(V₀^2/4))
  let K := max (4*(j:ℝ)) (4*(j:ℝ)/Real.log 2)
  have hc : 0<c := (giantCandidateCoinScale_bounds hq₀ hq₁ j hj).1
  have hR : 0<R := Real.exp_pos _
  have hlog₂ : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hV₀ : 0<V₀ := half_pos hlog₂
  refine ⟨β,by dsimp only [β]; positivity,?_⟩
  have hK := (Real.tendsto_exp_atTop.comp
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<28/100)).comp Real.tendsto_log_atTop)).eventually_ge_atTop K
  filter_upwards [hK,giantCandidateGroup_mass_eventually,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ)] with x hKx hmass hx hL
  intro g hp
  let P := giantCandidateGroup x g
  let V := bandReciprocalMass P
  have hV : V₀≤V := (hmass g).1.le
  have hbig (p : ℕ) (hp : p∈P) : K≤(p:ℝ) :=
    hKx.trans ((giantCandidateFullPrimes_range hx hL (mem_giantCandidateFullPrimes.mpr ⟨g,hp⟩)).2.1)
  have hlarge (p : ℕ) (hp : p∈P) : 4*(j:ℝ)≤(p:ℝ) := (le_max_left _ _).trans (hbig p hp)
  have hsmall (p : ℕ) (hp' : p∈P) : (j:ℝ)/(p:ℝ)≤V/2 := by
    have h := (div_le_iff₀ hlog₂).mp ((le_max_right _ _).trans (hbig p hp'))
    have hp₀ : (0:ℝ)<p := Nat.cast_pos.mpr (hp p hp').pos
    calc
      _ ≤ Real.log 2/4 := (div_le_iff₀ hp₀).mpr (by linarith only [h])
      _ ≤ V/2 := by
        dsimp only [V₀] at hV
        linarith only [hV]
  calc
    _ ≤ c*(R*(V^2/4)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (pow_le_pow_left₀ hV₀.le hV 2) (by norm_num)) hR.le) hc.le
    _ ≤ _ := giantCandidateSingleModelCoinMean_ge P hp hq₀ hq₁ hj hV (hmass g).2.le hlarge hsmall

end
end ArtinMatthews
