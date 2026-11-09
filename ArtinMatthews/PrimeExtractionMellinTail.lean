module

public import ArtinMatthews.PrimeExtractionMellinProfile


set_option backward.privateInPublic true
@[expose] public section

/-! Arbitrary polynomial frequency truncation for the actual smooth cutoff. -/

namespace ArtinMatthews

open Filter MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff

theorem prime_extraction_schwartz_tail (f : SchwartzMap ℝ ℂ) (k : ℕ)
    {H : ℝ} (hH : 0 < H) :
    (∫ t : ℝ in {t | H < |t|}, ‖f t‖) ≤
      (∫ t : ℝ, |t| ^ k * ‖f t‖) / H ^ k := by
  have hm : Integrable (fun t : ℝ => |t| ^ k * ‖f t‖) := by
    simpa only [Real.norm_eq_abs] using f.integrable_pow_mul volume k
  have hs : MeasurableSet {t : ℝ | H < |t|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  apply (le_div_iff₀ (pow_pos hH k)).mpr
  rw [← integral_mul_const]
  calc
    _ ≤ ∫ t : ℝ in {t | H < |t|}, |t| ^ k * ‖f t‖ := by
      apply setIntegral_mono_on (f.integrable.norm.mul_const _).integrableOn hm.integrableOn hs
      intro t ht
      dsimp at ht
      calc
        ‖f t‖ * H ^ k ≤ ‖f t‖ * |t| ^ k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH.le ht.le k) (norm_nonneg _)
        _ = _ := mul_comm _ _
    _ ≤ _ := setIntegral_le_integral hm (Eventually.of_forall (fun t => by positivity))

theorem primeExtractionMellinPhase_continuous (y : ℝ) :
    Continuous (fun t : ℝ => primeExtractionMellinPhase t y) := by
  unfold primeExtractionMellinPhase
  fun_prop

/-- Truncating at any H>0 costs at most the kth absolute Fourier moment
divided by H^k, uniformly in the positive argument y. -/
theorem primeExtraction_mellin_truncation (Φ : ℝ → ℂ) {a b : ℝ}
    (ha : 0 < a) (hsupp : Function.support Φ ⊆ Set.Icc a b) (hΦ : ContDiff ℝ ∞ Φ)
    (k : ℕ) {H y : ℝ} (hH : 0 < H) (hy : 0 < y) :
    ‖Φ y - ∫ t : ℝ in Set.Icc (-H) H,
      (𝓕 (primeExtractionLogProfile Φ ha hsupp hΦ)) t * primeExtractionMellinPhase t y‖ ≤
      (∫ t : ℝ, |t| ^ k * ‖(𝓕 (primeExtractionLogProfile Φ ha hsupp hΦ)) t‖) / H ^ k := by
  let f : SchwartzMap ℝ ℂ := 𝓕 (primeExtractionLogProfile Φ ha hsupp hΦ)
  have hint : Integrable (fun t : ℝ => f t * primeExtractionMellinPhase t y) :=
    f.integrable.mul_bdd (primeExtractionMellinPhase_continuous y).aestronglyMeasurable
      (Eventually.of_forall (fun t => (primeExtractionMellinPhase_norm t y).le))
  have hset : (Set.Icc (-H) H)ᶜ = {t : ℝ | H < |t|} := by
    ext t
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_ofPred_eq, not_and_or,
      not_le, lt_abs]
    constructor
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl h
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl (by linarith)
  calc
    _ = ‖∫ t : ℝ in (Set.Icc (-H) H)ᶜ, f t * primeExtractionMellinPhase t y‖ := by
      rw [setIntegral_compl measurableSet_Icc hint]
      rw [primeExtraction_mellin_inversion Φ ha hsupp hΦ hy]
    _ ≤ ∫ t : ℝ in (Set.Icc (-H) H)ᶜ, ‖f t * primeExtractionMellinPhase t y‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ t : ℝ in {t | H < |t|}, ‖f t‖ := by
      rw [hset]
      simp only [norm_mul, primeExtractionMellinPhase_norm, mul_one]
    _ ≤ _ := prime_extraction_schwartz_tail f k hH

end ArtinMatthews
