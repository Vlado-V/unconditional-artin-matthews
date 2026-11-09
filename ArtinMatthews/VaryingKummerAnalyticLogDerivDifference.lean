module

public import ArtinMatthews.VaryingKummerAnalyticComplexZeroPole
public import ArtinMatthews.VaryingKummerAnalyticPoleDifferenceBound


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine logarithmic-derivative bound away from the zeros, obtained by
taking limits of the actual finite pole sums. -/
namespace OAI.PrimeDegreePackets.AnalyticGrowth
open ArtinMatthews.ReusedGrowth Complex Set Filter
open scoped Topology BigOperators
noncomputable section

lemma norm_weighted_pole_difference_le {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1) {b s : ℂ} {δ : ℝ}
    (hb : b.re = 2) (hδ : 0 < δ)
    (hdist : ∀ ρ, f ρ = 0 → δ ≤ ‖s-ρ‖) (ρ : ℂ) :
    ‖(zeroMultiplicity f ρ : ℂ)*(1/(s-ρ)-1/(b-ρ))‖ ≤
      (‖b-s‖*(1+‖b-s‖/δ))*complexZeroPole f b ρ := by
  by_cases hm : zeroMultiplicity f ρ = 0
  · simp [hm, complexZeroPole]
  have hρ := (zeroMultiplicity_ne_zero_iff hf h0 ρ).mp hm
  have hnn : 0 ≤ (zeroMultiplicity f ρ : ℝ) := by
    exact_mod_cast zeroMultiplicity_nonneg hf ρ
  have hn : ‖(zeroMultiplicity f ρ : ℂ)‖ = (zeroMultiplicity f ρ : ℝ) := by
    rw [Complex.norm_intCast, abs_of_nonneg hnn]
  rw [norm_mul, hn]
  have H := mul_le_mul_of_nonneg_left
    (norm_pole_reciprocal_difference_le hb (hstrip ρ hρ) hδ (hdist ρ hρ)) hnn
  simpa only [complexZeroPole, mul_left_comm] using H

theorem norm_logDeriv_sub_le_of_zero_distance {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hg : HasSubquadraticGrowth f) (hfe : ∀ z, f (1-z) = f z)
    (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1) {b s : ℂ} {δ : ℝ}
    (hb : b.re = 2) (hδ : 0 < δ)
    (hdist : ∀ ρ, f ρ = 0 → δ ≤ ‖s-ρ‖) :
    ‖logDeriv f s-logDeriv f b‖ ≤
      (‖b-s‖*(1+‖b-s‖/δ))*(logDeriv f b).re := by
  classical
  have hb' : 1 < b.re := by rw [hb]; norm_num
  have hb0 : f b ≠ 0 := by
    intro H
    have := hstrip b H
    linarith
  have hs0 : f s ≠ 0 := by
    intro H
    have := hdist s H
    simp only [sub_self, norm_zero] at this
    linarith
  let C : ℝ := ‖b-s‖*(1+‖b-s‖/δ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have HS := hasSum_complexZeroPole hf h0 hg hfe hstrip hb'
  have HNN := complexZeroPole_nonneg hf h0 hstrip hb'
  have Hfinite (R : ℝ) :
      ‖diskPoleSum f R s-diskPoleSum f R b‖ ≤ C*(logDeriv f b).re := by
    rw [diskPoleSum, diskPoleSum, ← Finset.sum_sub_distrib]
    simp only [← mul_sub]
    calc
      _ ≤ ∑ ρ ∈ zeroDiskFinset f R,
          ‖(zeroMultiplicity f ρ : ℂ)*(1/(s-ρ)-1/(b-ρ))‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ zeroDiskFinset f R, C*complexZeroPole f b ρ := by
        apply Finset.sum_le_sum
        intro ρ _
        exact norm_weighted_pole_difference_le hf h0 hstrip hb hδ hdist ρ
      _ = C*∑ ρ ∈ zeroDiskFinset f R, complexZeroPole f b ρ := by rw [Finset.mul_sum]
      _ ≤ C*∑' ρ, complexZeroPole f b ρ := mul_le_mul_of_nonneg_left
        (HS.summable.sum_le_tsum _ (fun ρ _ => HNN ρ)) hC
      _ = _ := by rw [HS.tsum_eq]
  obtain ⟨r,hr,_,hS⟩ := exists_good_radii hf h0
  have HT := (tendsto_diskPoleSum_sub hf h0 hg hr
    (Filter.Eventually.of_forall hS) hs0 hb0).norm
  exact le_of_tendsto HT (Filter.Eventually.of_forall (fun i => Hfinite (r i)))

end
end OAI.PrimeDegreePackets.AnalyticGrowth
