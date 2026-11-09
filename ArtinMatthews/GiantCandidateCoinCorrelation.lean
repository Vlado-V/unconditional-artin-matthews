module

public import ArtinMatthews.GiantCandidateCoinExpansion


set_option backward.privateInPublic true
@[expose] public section

/-! Sum the square-exception errors over the actual performed signed
terms. The separate failed outcome mass is never multiplied by this
term count. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section

theorem giantCandidateRetainedProxy_signedCorrelation_log_saving {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ i,0 < e i ∧ e i < 1) {M : ℕ} (χ : DirichletCharacter ℂ M)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4) (Φ : ℝ → ℝ) (hΦ : Continuous Φ)
    {T γ q : ℝ} (hT : 0 ≤ T) (hΦzero : Φ 0=0) (hhigh : ∀ t,T<t → Φ t=0)
    (hγ : 0 < γ) (hq0 : 0 ≤ q) (hq1 : q < 1) (j : ℕ) (hj : 0 < j) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop,∀ threshold : ℝ,
      let c := giantCandidateCoinScale q j
      ‖giantCandidateWeightedStrippedProxy e χ ε Φ (T+1) γ j x
          (giantCandidateRetainedCoinMass x threshold c q j) -
        giantCandidateSignedCorrelationSum e χ ε Φ T γ j x threshold c q‖ ≤
          x*(Real.log x)^(-A) := by
  let c := giantCandidateCoinScale q j
  have hc' := giantCandidateCoinScale_bounds hq0 hq1 j hj
  have hc : c ∈ Set.Icc (0:ℝ) 1 := ⟨hc'.1.le,hc'.2.1⟩
  let b := giantCandidateGroupLogRate*Real.log 3
  filter_upwards [giantCandidateActualExpandedProxyTerm_shifted_log_saving e he χ hε hεq Φ hΦ
      hT hΦzero hhigh hγ hq0 hq1 j hj (A+b),
    giantCandidateCoinTerms_card_log_eventually,eventually_gt_atTop (1:ℝ)]
    with x hcorr hcard hx
  intro threshold
  let E := giantCandidateCoinTerms x threshold
  let L := Real.log x
  let a (p : GiantCandidateCoinTerm x) := giantCandidateCoinTermCoefficient x c p
  let P (p : GiantCandidateCoinTerm x) (i : ↥(p.1 ∪ p.2)) := giantCandidateGroup x i.val
  let C := giantCandidateFullPrimes x
  let f (p : GiantCandidateCoinTerm x) :=
    giantCandidateActualUnguardedMarkedProxyTerm C (P p) e χ ε Φ (T+1) γ q j x
  let g (p : GiantCandidateCoinTerm x) := ((j:ℂ)^(p.1 ∪ p.2).card/j.factorial) *
    ((x:ℂ)*giantCandidateActualUnguardedShiftedCorrelation C (P p) e χ ε Φ T γ q j x)
  have hL : 0 < L := Real.log_pos hx
  have hterm (p : GiantCandidateCoinTerm x) : ‖a p*(f p-g p)‖ ≤ x*L^(-(A+b)) := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (giantCandidateCoinTermCoefficient_norm_le_one x hc p)).trans (hcorr (p.1 ∪ p.2))
  dsimp only
  rw [giantCandidateRetainedStrippedProxy_eq_expansion,giantCandidateSignedCorrelationSum]
  change ‖(∑ p ∈ E,a p*f p)-(∑ p ∈ E,a p*g p)‖ ≤ _
  rw [← sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∑ p ∈ E,‖a p*(f p-g p)‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ E,x*L^(-(A+b)) := sum_le_sum (fun p _ => hterm p)
    _ = (E.card:ℝ)*(x*L^(-(A+b))) := by rw [sum_const,nsmul_eq_mul]
    _ ≤ L^b*(x*L^(-(A+b))) := mul_le_mul_of_nonneg_right (hcard threshold) (by positivity)
    _ = x*(L^b*L^(-(A+b))) := by ring
    _ = _ := by rw [← Real.rpow_add hL]; congr 2; ring

theorem giantCandidateStrippedProxy_signedCorrelation_error {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ i,0 < e i ∧ e i < 1) {M : ℕ} (χ : DirichletCharacter ℂ M)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4) (Φ : ℝ → ℝ) (hΦ : Continuous Φ)
    {T γ q : ℝ} (hT : 0 ≤ T) (hΦzero : Φ 0=0) (hhigh : ∀ t,T<t → Φ t=0)
    (hγ : 0 < γ) (hq0 : 0 ≤ q) (hq1 : q < 1) (j : ℕ) (hj : 0 < j) (A : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ x : ℝ in atTop,∀ threshold : ℝ,
      let c := giantCandidateCoinScale q j
      ‖giantOrdinaryStrippedProxyTupleSum giantCandidateFullPrimes e χ
        (giantMarkedCenteredCore ε) Φ (T+1) γ j x -
          giantCandidateSignedCorrelationSum e χ ε Φ T γ j x threshold c q‖ ≤
        D*giantCandidateFailedProxyMass x threshold c q (T+1) γ j +
          x*(Real.log x)^(-A) := by
  have hT1 : 0 ≤ T+1 := by positivity
  obtain ⟨D,hD,hfail⟩ := giantCandidateFailedProxyError_bound e he χ hε hεq Φ hΦ hT1 γ hq0 hq1 j hj
  refine ⟨D,hD,?_⟩
  filter_upwards [hfail,giantCandidateRetainedProxy_signedCorrelation_log_saving e he χ hε hεq Φ hΦ
    hT hΦzero hhigh hγ hq0 hq1 j hj A] with x hf hg
  intro threshold
  let c := giantCandidateCoinScale q j
  let F := giantCandidateWeightedStrippedProxy e χ ε Φ (T+1) γ j x
    (giantCandidateFailedCoinMass x threshold c q j)
  let R := giantCandidateWeightedStrippedProxy e χ ε Φ (T+1) γ j x
    (giantCandidateRetainedCoinMass x threshold c q j)
  let S := giantCandidateSignedCorrelationSum e χ ε Φ T γ j x threshold c q
  dsimp only
  rw [giantCandidateStrippedProxy_partition e χ ε Φ (T+1) γ j x threshold c q]
  change ‖(R+F)-S‖ ≤ _
  rw [add_comm R F,add_sub_assoc]
  exact (norm_add_le F (R-S)).trans (add_le_add (hf threshold) (hg threshold))

end
end ArtinMatthews
