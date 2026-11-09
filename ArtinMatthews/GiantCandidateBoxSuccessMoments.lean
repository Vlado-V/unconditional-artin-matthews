module

public import ArtinMatthews.GiantCandidateSingleCoinLower
public import ArtinMatthews.GiantCandidateActualCoinCovariance


set_option backward.privateInPublic true
@[expose] public section

/-! The actual full rough boxes have uniform positive coin means and
vanishing off-diagonal covariance. -/

namespace ArtinMatthews
noncomputable section
open Filter Finset
open scoped BigOperators

theorem giant_candidate_box_success_moments_eventually (τ : ℝ) (hτ : 0<τ)
    {q : ℝ} (hq₀ : 0≤q) (hq₁ : q<1) {j : ℕ} (hj : 0<j) :
    ∃ β : ℝ,0<β ∧ ∀ δ : ℝ,0<δ →
      ∀ᶠ x : ℝ in atTop,∀ H : Fin j → ℕ,(∀v,x^τ≤(H v:ℝ)) →
        let S := giantCandidateFullRoughBox x H
        let s (t : Fin j → ℕ) (g : GiantCandidateGroupIndex x) :=
          giantCandidateCoinSuccess x (giantCandidateCoinScale q j) q j (∏v,t v) g
        (∀ g : GiantCandidateGroupIndex x,β≤𝔼 t∈S,s t g) ∧
        ∀ g h : GiantCandidateGroupIndex x,g≠h →
          |(𝔼 t∈S,s t g*s t h)-(𝔼 t∈S,s t g)*(𝔼 t∈S,s t h)|≤δ := by
  obtain ⟨b,hb,hmodel⟩ := giant_candidate_single_model_coin_mean_lower_eventually hq₀ hq₁ hj
  refine ⟨b/2,half_pos hb,?_⟩
  intro δ hδ
  filter_upwards [hmodel,
    giant_candidate_actual_single_coin_compare_eventually τ hτ hq₀ hq₁ hj (half_pos hb),
    giant_candidate_box_coin_covariance_eventually τ hτ hq₀ hq₁ hj hδ,
    giantCandidateFullPrimes_prime_upper_eventually] with x hlo hsingle hcov hP
  intro H hH S s
  constructor
  · intro g
    have hp : ∀p∈giantCandidateGroup x g,p.Prime := fun p hp =>
      (hP p (mem_giantCandidateFullPrimes.mpr ⟨g,hp⟩)).1
    let m := giantCandidateSingleModelCoinMean (giantCandidateGroup x g) hp
      (giantCandidateCoinScale q j) q j
    have hm : b ≤ m := hlo g hp
    have hh : |(𝔼 t∈S,s t g)-m|≤b/2 := hsingle g hp H hH
    linarith only [hm,(abs_le.mp hh).1]
  · exact hcov H hH

end
end ArtinMatthews
