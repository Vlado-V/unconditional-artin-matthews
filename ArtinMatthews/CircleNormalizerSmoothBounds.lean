module

public import ArtinMatthews.CircleNormalizer
public import ArtinMatthews.CircleNormalizerSmooth


set_option backward.privateInPublic true
@[expose] public section

/-! The concrete smooth cutoff satisfies the actual circle-normalizer estimates. -/

noncomputable section
namespace ArtinMatthews

theorem circleSmoothNormalizer_lower (ε : ℝ) (hε : 0 < ε) (hεone : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ F r L : ℕ, 0 < F → 0 < r → F.Coprime r →
      4 * (F * r) ≤ L →
      C * (L : ℝ)^(2-ε) / ((F : ℝ)*(r : ℝ)^ε) ≤
        circleNormalizer (circleModuli F r L) (circleSmoothWeight L) := by
  obtain ⟨C, hC, hbound⟩ := circleNormalizer_lower ε hε hεone
  refine ⟨C, hC, fun F r L hF hr hFr hL => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity : 0 < 4 * (F * r)) hL
  exact hbound F r L hF hr hFr hL (circleSmoothWeight L)
    (fun q _ => circleSmoothWeight_nonneg L q)
    (fun q hq1 hq2 => (circleSmoothWeight_plateau hLpos hq1 hq2).symm.le)

theorem circleSmoothNormalizer_positive {F r L : ℕ} (hF : 0 < F) (hr : 0 < r)
    (hFr : F.Coprime r) (hL : 4 * (F * r) ≤ L) :
    0 < circleNormalizer (circleModuli F r L) (circleSmoothWeight L) := by
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity : 0 < 4 * (F * r)) hL
  exact circleNormalizer_positive hF hr hFr hL (circleSmoothWeight L)
    (fun q _ => circleSmoothWeight_nonneg L q)
    (fun q hq1 hq2 => (circleSmoothWeight_plateau hLpos hq1 hq2).symm.le)

theorem circleSmoothWeightMass_le {F r L : ℕ} (hL : 1 ≤ L) :
    circleWeightMass (circleModuli F r L) (circleSmoothWeight L) ≤ 4 * L := by
  simpa only [mul_one] using circleModuli_weightMass_le F r L hL (circleSmoothWeight L)
    1 zero_le_one (fun q _ => circleSmoothWeight_le_one L q)

end ArtinMatthews
