module

public import ArtinMatthews.PrimeExtractionMellinBilinear


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform polynomial and logarithmic frequency truncation for the actual
finite bilinear Mellin separation. -/

noncomputable section
namespace ArtinMatthews

open Filter MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap ContDiff

theorem primeExtraction_bilinear_mellin_truncation (Φ : ℝ → ℂ) {a b : ℝ}
    (ha : 0 < a) (hsupp : Function.support Φ ⊆ Set.Icc a b) (hΦ : ContDiff ℝ ∞ Φ)
    (M N : Finset ℕ) (A : ℕ → ℕ → ℂ) (k : ℕ) {H x : ℝ} (hH : 0 < H) (hx : 0 < x)
    (hM : ∀ m ∈ M, 0 < m) (hN : ∀ n ∈ N, 0 < n) :
    ‖(∑ m ∈ M, ∑ n ∈ N, A m n * Φ (((m*n : ℕ) : ℝ)/x)) -
      ∫ t : ℝ in Set.Icc (-H) H, (𝓕 (primeExtractionLogProfile Φ ha hsupp hΦ)) t *
        primeExtractionMellinPhase (-t) x * primeExtractionBilinearPhaseSum M N A t‖ ≤
      ((∫ t : ℝ, |t|^k * ‖(𝓕 (primeExtractionLogProfile Φ ha hsupp hΦ)) t‖) / H^k) *
        primeExtractionBilinearMass M N A := by
  classical
  let f : SchwartzMap ℝ ℂ := 𝓕 (primeExtractionLogProfile Φ ha hsupp hΦ)
  let D : ℝ := (∫ t : ℝ, |t|^k * ‖f t‖) / H^k
  let E : ℕ → ℕ → ℂ := fun m n => Φ (((m*n : ℕ) : ℝ)/x) -
    ∫ t : ℝ in Set.Icc (-H) H, f t * primeExtractionMellinPhase t (((m*n : ℕ) : ℝ)/x)
  have heq : (∑ m ∈ M, ∑ n ∈ N, A m n * Φ (((m*n : ℕ) : ℝ)/x)) -
      (∫ t : ℝ in Set.Icc (-H) H, f t * primeExtractionMellinPhase (-t) x *
        primeExtractionBilinearPhaseSum M N A t) =
      ∑ m ∈ M, ∑ n ∈ N, A m n * E m n := by
    rw [← primeExtraction_bilinear_setIntegral f M N A (Set.Icc (-H) H) hx hM hN]
    simp only [E, mul_sub, Finset.sum_sub_distrib]
  change ‖(∑ m ∈ M, ∑ n ∈ N, A m n * Φ (((m*n : ℕ) : ℝ)/x)) -
      (∫ t : ℝ in Set.Icc (-H) H, f t * primeExtractionMellinPhase (-t) x *
        primeExtractionBilinearPhaseSum M N A t)‖ ≤ D * primeExtractionBilinearMass M N A
  rw [heq]
  calc
    _ ≤ ∑ m ∈ M, ∑ n ∈ N, ‖A m n * E m n‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ m ∈ M, ∑ n ∈ N, ‖A m n‖ * D := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have hy : 0 < (((m*n : ℕ) : ℝ)/x) :=
        div_pos (by exact_mod_cast Nat.mul_pos (hM m hm) (hN n hn)) hx
      exact primeExtraction_mellin_truncation Φ ha hsupp hΦ k hH hy
    _ = primeExtractionBilinearMass M N A * D := by
      simp only [primeExtractionBilinearMass, Finset.sum_mul]
    _ = _ := mul_comm _ _

/-- A logarithmic-height cutoff retains every desired absolute Fourier
moment, with its exact power and the actual finite coefficient mass. -/
theorem primeExtraction_bilinear_mellin_log_truncation (Φ : ℝ → ℂ) {a b : ℝ}
    (ha : 0 < a) (hsupp : Function.support Φ ⊆ Set.Icc a b) (hΦ : ContDiff ℝ ∞ Φ)
    (M N : Finset ℕ) (A : ℕ → ℕ → ℂ) (j k : ℕ) {x : ℝ} (hx : 1 < x)
    (hM : ∀ m ∈ M, 0 < m) (hN : ∀ n ∈ N, 0 < n) :
    ‖(∑ m ∈ M, ∑ n ∈ N, A m n * Φ (((m*n : ℕ) : ℝ)/x)) -
      ∫ t : ℝ in Set.Icc (-(Real.log x)^j) ((Real.log x)^j),
        (𝓕 (primeExtractionLogProfile Φ ha hsupp hΦ)) t *
          primeExtractionMellinPhase (-t) x * primeExtractionBilinearPhaseSum M N A t‖ ≤
      ((∫ t : ℝ, |t|^k * ‖(𝓕 (primeExtractionLogProfile Φ ha hsupp hΦ)) t‖) *
        primeExtractionBilinearMass M N A) / (Real.log x)^(j*k) := by
  have h := primeExtraction_bilinear_mellin_truncation Φ ha hsupp hΦ M N A k
    (pow_pos (Real.log_pos hx) j) (by linarith : 0 < x) hM hN
  rw [← pow_mul] at h
  convert h using 1
  ring

end ArtinMatthews
