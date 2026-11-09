module

public import ArtinMatthews.VaryingKummerAnalyticZeroHeightWindow


set_option backward.privateInPublic true
@[expose] public section

/-! The actual multiplicity count bounds the number of distinct bad heights. -/
namespace OAI.PrimeDegreePackets.AnalyticGrowth
open ArtinMatthews.ReusedGrowth Complex
open scoped BigOperators
noncomputable section

lemma zeroHeightWindow_card_le {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hfe : ∀ z, f (1-z) = f z)
    (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1) (T : ℝ) :
    ((zeroHeightWindow f T).card : ℝ) ≤ zeroHeightCount f T := by
  unfold zeroHeightCount
  calc
    _ = ∑ ρ ∈ zeroHeightWindow f T, (1 : ℝ) := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro ρ hρ
      have hz := ((mem_zeroHeightWindow_iff hf h0 hfe hstrip T ρ).mp hρ).1
      have hm := (zeroMultiplicity_ne_zero_iff hf h0 ρ).mpr hz
      have hp : (1 : ℤ) ≤ zeroMultiplicity f ρ := by
        have hn := zeroMultiplicity_nonneg hf ρ
        omega
      exact_mod_cast hp

lemma zeroHeightImaginary_card_le {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hfe : ∀ z, f (1-z) = f z)
    (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1) (T : ℝ) :
    (((zeroHeightWindow f T).image Complex.im).card : ℝ) ≤ zeroHeightCount f T := by
  have hc : (((zeroHeightWindow f T).image Complex.im).card : ℝ) ≤
      ((zeroHeightWindow f T).card : ℝ) := by exact_mod_cast Finset.card_image_le
  exact hc.trans (zeroHeightWindow_card_le hf h0 hfe hstrip T)

end
end OAI.PrimeDegreePackets.AnalyticGrowth
