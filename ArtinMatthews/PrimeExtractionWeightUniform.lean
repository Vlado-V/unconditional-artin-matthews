module

public import ArtinMatthews.PrimeExtractionWeightBounds


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform boundedness of the actual cutoff, marking array, and core
weight on the finite extraction interval. -/

namespace ArtinMatthews

open Filter

noncomputable def markedExtractionWeight {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℂ :=
  (Φ (((n - 1 : ℕ) : ℝ) / x) : ℂ) * (literalMarkedArrayWeight e x (n - 1) : ℂ) * G x (n - 1)

theorem markedExtractionWeight_bound {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (he : ∀ i, 0 < e i) (G : ℝ → ℕ → ℂ)
    {CG : ℝ} (hCG : 0 ≤ CG) (hG : ∀ᶠ x : ℝ in atTop, ∀ u : ℕ, ‖G x u‖ ≤ CG)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, (n : ℝ) ≤ T * x →
      ‖markedExtractionWeight e G Φ x n‖ ≤ C := by
  obtain ⟨CΦ, hCΦ⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hΦ.continuousOn : ContinuousOn Φ (Set.Icc 0 T))
  have hCΦ0 : 0 ≤ CΦ := (norm_nonneg (Φ 0)).trans (hCΦ 0 ⟨le_rfl, hT⟩)
  let W := (2 / Real.log 2) ^ Fintype.card ι
  have hW0 : 0 ≤ W := by dsimp [W]; positivity
  refine ⟨CΦ * W * CG, mul_nonneg (mul_nonneg hCΦ0 hW0) hCG, ?_⟩
  filter_upwards [literalMarkedArrayWeight_bound_eventually e he, hG,
    eventually_gt_atTop (0 : ℝ)] with x hW hGx hx
  intro n hnT
  have harg : ((n - 1 : ℕ) : ℝ) / x ∈ Set.Icc 0 T :=
    ⟨div_nonneg (Nat.cast_nonneg _) hx.le,
      (div_le_iff₀ hx).mpr ((Nat.cast_le.mpr (Nat.sub_le n 1)).trans hnT)⟩
  have hphi : ‖(Φ (((n - 1 : ℕ) : ℝ) / x) : ℂ)‖ ≤ CΦ := by
    simpa only [Complex.norm_real] using hCΦ _ harg
  have hweight : ‖(literalMarkedArrayWeight e x (n - 1) : ℂ)‖ ≤ W := by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (literalMarkedArrayWeight_nonneg e x (n - 1))] using hW (n - 1)
  unfold markedExtractionWeight
  simp only [norm_mul]
  exact mul_le_mul (mul_le_mul hphi hweight (norm_nonneg _) hCΦ0)
    (hGx _) (norm_nonneg _) (mul_nonneg hCΦ0 hW0)

end ArtinMatthews
